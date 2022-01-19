from typing import Iterable, List

import numpy as np
from sortedcontainers import SortedList

from syma.alphabet import Interval


class ValuationSet:
    """This is used to define a set of intervals where a specific variable's
    valuations hold true for some predicate.
    """

    def __init__(self, intervals: Iterable[Interval]) -> None:
        self._ints = SortedList()  # type: List[Interval]
        for i in intervals:
            if i.is_empty():
                continue
            self._ints.add(i)

        self._simplify()

    def __contains__(self, val: float) -> bool:
        for i in self._ints:
            if val in i:
                return True
        return False

    def contains_interval(self, interval: Interval) -> bool:
        low, high = interval.as_tuple()
        for i in self._ints:
            if (low in i) and (high in i):
                return True
        return False

    def is_empty(self) -> bool:
        if len(self._ints) == 0:
            return True
        else:
            return all(not i.is_empty() for i in self._ints)

    def _simplify(self):
        ret: List[Interval] = []

        if self.is_empty():
            return ValuationSet(ret)
        # We know the intervals are sorted, so we can just merge if they overlap with
        # the previously added element, else just append.
        ret.append(self._ints[0])
        for interval in self._ints:
            assert not interval.is_empty()
            if ret[-1].is_disjoint(interval):
                ret.append(interval)
                continue
            else:
                merged = ret[-1].union(interval)
                assert len(merged) == 1
                ret.append(merged[0])
        self._ints = SortedList(ret)

    def intersection(self, other: "ValuationSet") -> "ValuationSet":
        # Essentially, we want to do a kind of merge step (similar to mergesort).

        # Alias the intervals
        ints_i = self._ints
        ints_j = other._ints
        # Indices into the intervals
        i = 0
        j = 0

        # Our output list
        ret: List[Interval] = []

        while (i < len(ints_i)) and (j < len(ints_j)):
            int_i = ints_i[i]
            int_j = ints_j[j]

            if int_i.is_empty():
                i += 1
                continue
            if int_j.is_empty():
                j += 1
                continue
            if int_i.is_disjoint(int_j):
                # They are disjoint, so discard the one that is to the left.
                if int_i < int_j:
                    i += 1
                else:
                    j += 1
                continue
            # They overlap. Intersect them then discard the one that has its high
            # within the other
            ret.append(int_i.intersect(int_j))
            if int_i.high < int_j.high:
                i += i
            else:
                j += 1

        return ValuationSet(ret)

    def union(self, other: "ValuationSet") -> "ValuationSet":
        # Since the valuation set is inherently a union-find structure, we just need
        # to concatenate the interval lists, and create a new ValuationSet. The
        # _simplify method called in the initialization will create the disjoing union
        # for us.

        ret: List[Interval] = []
        ret.extend(self._ints)
        ret.extend(other._ints)

        return ValuationSet(ret)

    @property
    def low(self) -> float:
        return self._ints[0].low

    @property
    def high(self) -> float:
        return self._ints[-1].high

    def is_bounded(self) -> bool:
        if np.isinf(abs(self.low)) or np.isinf(abs(self.high)):
            return False
        else:
            return True

    def is_unbounded(self) -> bool:
        return not self.is_bounded()
