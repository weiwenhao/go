// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Central free lists.
//
// See malloc.go for an overview.
//
// The mcentral doesn't actually contain the list of free objects; the mspan does.
// Each mcentral is two lists of mspans: those with free objects (c->nonempty)
// and those that are completely allocated (c->empty).

package runtime

import "runtime/internal/atomic"

// Central list of free objects of a given size.
//
//go:notinheap
type mcentral struct {
	spanclass spanClass

	// partial and full contain two mspan sets: one of swept in-use
	// spans, and one of unswept in-use spans. These two trade
	// roles on each GC cycle. The unswept set is drained either by
	// allocation or by the background sweeper in every GC cycle,
	// so only two roles are necessary.
	// [2]spanset 主要是为了 gc 考虑
	// sweepgen is increased by 2 on each GC cycle, so the swept
	// spans are in partial[sweepgen/2%2] and the unswept spans are in
	// partial[1-sweepgen/2%2]. Sweeping pops spans from the
	// unswept set and pushes spans that are still in-use on the
	// swept set. Likewise, allocating an in-use span pushes it
	// on the swept set.
	//
	// Some parts of the sweeper can sweep arbitrary spans, and hence
	// can't remove them from the unswept set, but will add the span
	// to the appropriate swept list. As a result, the parts of the
	// sweeper and mcentral that do consume from the unswept list may
	// encounter swept spans, and these should be ignored.
	// 为什么要包含两个 span 即可？
	partial [2]spanSet // list of spans with a free object  // 包含空闲的 object 的 span?
	full    [2]spanSet // list of spans with no free objects  // 全部用满 object 的 span 集合？
}

// Initialize a single central free list.
func (c *mcentral) init(spc spanClass) {
	c.spanclass = spc
	lockInit(&c.partial[0].spineLock, lockRankSpanSetSpine)
	lockInit(&c.partial[1].spineLock, lockRankSpanSetSpine)
	lockInit(&c.full[0].spineLock, lockRankSpanSetSpine)
	lockInit(&c.full[1].spineLock, lockRankSpanSetSpine)
}

// partialUnswept returns the spanSet which holds partially-filled
// unswept spans for this sweepgen.
func (c *mcentral) partialUnswept(sweepgen uint32) *spanSet {
	return &c.partial[1-sweepgen/2%2]
}

// partialSwept returns the spanSet which holds partially-filled
// swept spans for this sweepgen.
// 读取已经 swept 的 span
func (c *mcentral) partialSwept(sweepgen uint32) *spanSet {
	return &c.partial[sweepgen/2%2]
}

// fullUnswept returns the spanSet which holds unswept spans without any
// free slots for this sweepgen.
func (c *mcentral) fullUnswept(sweepgen uint32) *spanSet {
	return &c.full[1-sweepgen/2%2]
}

// fullSwept returns the spanSet which holds swept spans without any
// free slots for this sweepgen.
func (c *mcentral) fullSwept(sweepgen uint32) *spanSet {
	return &c.full[sweepgen/2%2]
}

// Allocate a span to use in an mcache.
func (c *mcentral) cacheSpan() *mspan {
	// Deduct credit for this span allocation and sweep if necessary.
	// 根据 size class 选择合适的 pages 的大小, 同一个 size class 下的 pages 大小是确定的(8k 的 倍数)
	// 这里的 span pages 值得是单个 span 中包含的内存数量
	spanBytes := uintptr(class_to_allocnpages[c.spanclass.sizeclass()]) * _PageSize
	deductSweepCredit(spanBytes, 0)

	traceDone := false
	if trace.enabled {
		traceGCSweepStart()
	}

	// If we sweep spanBudget spans without finding any free
	// space, just allocate a fresh span. This limits the amount
	// of time we can spend trying to find free space and
	// amortizes the cost of small object sweeping over the
	// benefit of having a full free span to allocate from. By
	// setting this to 100, we limit the space overhead to 1%.
	//
	// TODO(austin,mknyszek): This still has bad worst-case
	// throughput. For example, this could find just one free slot
	// on the 100th swept span. That limits allocation latency, but
	// still has very poor throughput. We could instead keep a
	// running free-to-used budget and switch to fresh span
	// allocation if the budget runs low.
	spanBudget := 100

	var s *mspan
	var sl sweepLocker

	// Try partial swept spans first.
	// 如果在 mcentral partial 中找到了就直接返回
	// sg == sweepgen 表示当前轮的 gc 已经完成
	sg := mheap_.sweepgen
	// 如果 mcentral 中有已经清扫过的 swept, 直接使用
	if s = c.partialSwept(sg).pop(); s != nil { // 包含空闲的 paritial span
		goto havespan
	}

	// mheap grow 逻辑
	sl = sweep.active.begin()
	if sl.valid {
		// Now try partial unswept spans.
		for ; spanBudget >= 0; spanBudget-- {
			s = c.partialUnswept(sg).pop()
			if s == nil {
				break
			}
			if s, ok := sl.tryAcquire(s); ok {
				// We got ownership of the span, so let's sweep it and use it.
				s.sweep(true)
				sweep.active.end(sl)
				goto havespan
			}
			// We failed to get ownership of the span, which means it's being or
			// has been swept by an asynchronous sweeper that just couldn't remove it
			// from the unswept list. That sweeper took ownership of the span and
			// responsibility for either freeing it to the heap or putting it on the
			// right swept list. Either way, we should just ignore it (and it's unsafe
			// for us to do anything else).
		}
		// Now try full unswept spans, sweeping them and putting them into the
		// right list if we fail to get a span.
		for ; spanBudget >= 0; spanBudget-- {
			s = c.fullUnswept(sg).pop()
			if s == nil {
				break
			}
			if s, ok := sl.tryAcquire(s); ok {
				// We got ownership of the span, so let's sweep it.
				s.sweep(true)
				// Check if there's any free space.
				freeIndex := s.nextFreeIndex()
				if freeIndex != s.nelems {
					s.freeindex = freeIndex
					sweep.active.end(sl)
					goto havespan
				}
				// Add it to the swept list, because sweeping didn't give us any free space.
				c.fullSwept(sg).push(s.mspan)
			}
			// See comment for partial unswept spans.
		}
		sweep.active.end(sl)
	}
	if trace.enabled {
		traceGCSweepDone()
		traceDone = true
	}

	// We failed to get a span from the mcentral so get one from mheap.
	// mcentral 中已经没有可用的 span 了，从 mheap 中申请咯
	s = c.grow()
	if s == nil {
		return nil
	}

	// At this point s is a span that should have free slots.
	// 变量 s 引用的 span 有空闲的 slot
havespan:
	if trace.enabled && !traceDone {
		traceGCSweepDone()
	}
	n := int(s.nelems) - int(s.allocCount) // 重复判断一下是否有空闲的位置,没有就是有异常
	if n == 0 || s.freeindex == s.nelems || uintptr(s.allocCount) == s.nelems {
		throw("span has no free objects")
	}
	freeByteBase := s.freeindex &^ (64 - 1)
	whichByte := freeByteBase / 8
	// Init alloc bits cache.
	s.refillAllocCache(whichByte)

	// Adjust the allocCache so that s.freeindex corresponds to the low bit in
	// s.allocCache.
	s.allocCache >>= s.freeindex % 64

	return s
}

// Return span from an mcache.
//
// s must have a span class corresponding to this
// mcentral and it must not be empty.
func (c *mcentral) uncacheSpan(s *mspan) {
	if s.allocCount == 0 {
		throw("uncaching span but s.allocCount == 0")
	}

	// 判断当前 span 的 gc 状态
	// 每进行一轮 gc, sweepgen 的值就 + 2， 通过该值能够判断每一个 span 的当前处于 gc 的哪一个阶段
	sg := mheap_.sweepgen
	//  the span was cached before sweep began and is still cached, and needs sweeping
	// sweep generation:
	// if sweepgen == h->sweepgen - 2, the span needs sweeping // 需要 gc
	// if sweepgen == h->sweepgen - 1, the span is currently being swept // span 正在进行 gc
	// if sweepgen == h->sweepgen, the span is swept and ready to use // 已经 gc 扫描了所有的 object，并且 span 可以被使用。 被谁使用？

	// span 被 mcache 使用，现在仍然被 mcache 持有，需要 swepping
	// if sweepgen == h->sweepgen + 1, the span was cached before sweep began and is still cached, and needs sweeping

	// span 被 swept 之后被 mcache 缓存，现在仍然被 cached
	// if sweepgen == h->sweepgen + 3, the span was swept and then cached and is still cached
	// h->sweepgen is incremented by 2 after every GC

	// 当前 span 被 mcache 持有，需要 sweep
	stale := s.sweepgen == sg+1

	// Fix up sweepgen.
	if stale {
		// Span was cached before sweep began. It's our
		// responsibility to sweep it.
		//
		// Set sweepgen to indicate it's not cached but needs
		// sweeping and can't be allocated from. sweep will
		// set s.sweepgen to indicate s is swept.
		atomic.Store(&s.sweepgen, sg-1) // - 1 就是正在进行 gc
	} else {
		// Indicate that s is no longer cached.
		atomic.Store(&s.sweepgen, sg) // 当前 span 已经被 gc 扫过了，扫过了就说明真的没有空余的 span 了，立刻 uncache span 吧
	}

	// Put the span in the appropriate place.
	if stale {
		// It's stale, so just sweep it. Sweeping will put it on
		// the right list.
		//
		// We don't use a sweepLocker here. Stale cached spans
		// aren't in the global sweep lists, so mark termination
		// itself holds up sweep completion until all mcaches
		// have been swept.
		ss := sweepLocked{s} // 包裹起来进行 sweep
		ss.sweep(false)      // 上一步已经锁住了，现在开始进行 gc 咯
	} else {
		// 让 span 回归到 mcentral 的管理中
		if int(s.nelems)-int(s.allocCount) > 0 {
			// 虽然不知道为啥，但是目前还是有一定的空余的！为啥会有空余？被 mcache 持有的 span 难道也有 sweep?
			// Put it back on the partial swept list.
			c.partialSwept(sg).push(s)
		} else {
			// 完全没有空余咯
			// There's no free space and it's not stale, so put it on the
			// full swept list.
			c.fullSwept(sg).push(s)
		}
	}
}

// grow allocates a new empty span from the heap and initializes it for c's size class.
func (c *mcentral) grow() *mspan {
	npages := uintptr(class_to_allocnpages[c.spanclass.sizeclass()])
	size := uintptr(class_to_size[c.spanclass.sizeclass()])

	s := mheap_.alloc(npages, c.spanclass)
	if s == nil {
		return nil
	}

	// Use division by multiplication and shifts to quickly compute:
	// n := (npages << _PageShift) / size
	n := s.divideByElemSize(npages << _PageShift)
	s.limit = s.base() + size*n
	heapBitsForAddr(s.base()).initSpan(s)
	return s
}
