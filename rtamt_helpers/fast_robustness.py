from collections import deque
from typing import Dict, Mapping, Sequence, Union

import numpy as np
import numpy.typing as npt
from rtamt.node.abstract_node import AbstractNode
from rtamt.node.arithmetic.abs import Abs
from rtamt.node.arithmetic.addition import Addition
from rtamt.node.arithmetic.division import Division
from rtamt.node.arithmetic.exp import Exp
from rtamt.node.arithmetic.multiplication import Multiplication
from rtamt.node.arithmetic.pow import Pow
from rtamt.node.arithmetic.sqrt import Sqrt
from rtamt.node.arithmetic.subtraction import Subtraction
from rtamt.node.ltl.always import Always
from rtamt.node.ltl.conjunction import Conjunction
from rtamt.node.ltl.constant import Constant
from rtamt.node.ltl.disjunction import Disjunction
from rtamt.node.ltl.eventually import Eventually
from rtamt.node.ltl.fall import Fall
from rtamt.node.ltl.historically import Historically
from rtamt.node.ltl.iff import Iff
from rtamt.node.ltl.implies import Implies
from rtamt.node.ltl.neg import Neg
from rtamt.node.ltl.next import Next
from rtamt.node.ltl.once import Once
from rtamt.node.ltl.predicate import Predicate
from rtamt.node.ltl.previous import Previous
from rtamt.node.ltl.rise import Rise
from rtamt.node.ltl.since import Since
from rtamt.node.ltl.until import Until
from rtamt.node.ltl.variable import Variable
from rtamt.node.ltl.xor import Xor
from rtamt.node.stl.timed_always import TimedAlways
from rtamt.node.stl.timed_eventually import TimedEventually
from rtamt.node.stl.timed_historically import TimedHistorically
from rtamt.node.stl.timed_once import TimedOnce
from rtamt.node.stl.timed_precedes import TimedPrecedes
from rtamt.node.stl.timed_since import TimedSince
from rtamt.node.stl.timed_until import TimedUntil
from rtamt.spec.stl.discrete_time.comp_op import StlComparisonOperator
from rtamt.spec.stl.discrete_time.visitor import STLVisitor

NOT_IMPLEMENTED = "You should implement this."


def supermaxmin(a, w):
    """
    # a: array to compute filter over
    # w: window width

    >>> a = [9, 0, 5, 1, 11, 23, 55, 4, 16, 47, 33]
    >>> w = 3
    >>> supermaxmin(a, w)
    ([9, 5, 11, 23, 55, 55, 55, 47, 47], [0, 0, 1, 1, 11, 4, 4, 4, 16])
    """
    maxfifo, minfifo = deque((0,)), deque((0,))
    lena = len(a)
    maxvalues = [None] * (lena - w + 1)
    minvalues = [None] * (lena - w + 1)
    for i in range(1, lena):
        if i >= w:
            maxvalues[i - w] = a[maxfifo[0]]
            minvalues[i - w] = a[minfifo[0]]
        if a[i] > a[i - 1]:
            maxfifo.pop()
            while maxfifo:
                if a[i] <= a[maxfifo[-1]]:
                    break
                maxfifo.pop()
        else:
            minfifo.pop()
            while minfifo:
                if a[i] >= a[minfifo[-1]]:
                    break
                minfifo.pop()
        maxfifo.append(i)
        minfifo.append(i)
        if i == (w + maxfifo[0]):
            maxfifo.popleft()
        elif i == (w + minfifo[0]):
            minfifo.popleft()
        maxvalues[lena - w] = a[maxfifo[0]]
        minvalues[lena - w] = a[minfifo[0]]
    return maxvalues, minvalues


class _FastRobustness(STLVisitor):
    def __init__(self, trace: Mapping[str, Sequence[Union[int, float]]]) -> None:
        super().__init__()

        self.trace: Dict[str, npt.NDArray[np.float_]] = dict()
        for sig in trace:
            self.trace[sig] = np.asarray(trace[sig])
        self.trace_len: int = min(len(sig) for sig in trace.values())

    def compute(self, spec: AbstractNode) -> float:
        rob = self.visit(spec)
        return rob[0]

    def visit(self, spec: AbstractNode) -> npt.NDArray[np.float_]:
        return super().visit(spec, ())

    def visitPredicate(self, element: Predicate, _) -> npt.NDArray[np.float_]:
        lhs, rhs = self.visit(element.children[0]), self.visit(element.children[1])
        op = StlComparisonOperator(element.operator)
        assert len(lhs) == len(rhs)

        if op == StlComparisonOperator.LEQ:
            return rhs - lhs
        elif op == StlComparisonOperator.LESS:
            return rhs - lhs
        elif op == StlComparisonOperator.GEQ:
            return lhs - rhs
        elif op == StlComparisonOperator.GREATER:
            return lhs - rhs
        elif op == StlComparisonOperator.EQUAL:
            return np.asarray(lhs == rhs, dtype=int)
        elif op == StlComparisonOperator.NEQ:
            return np.asarray(lhs != rhs, dtype=int)
        else:
            raise ValueError(f"No idea what operation this is: {op}")

    def visitVariable(self, element: Variable, args) -> npt.NDArray[np.float_]:
        return self.trace[element.var]

    def visitAbs(self, element: Abs, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitSqrt(self, element: Sqrt, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitPow(self, element: Pow, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitExp(self, element: Exp, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitAddition(self, element: Addition, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitSubtraction(self, element: Subtraction, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitMultiplication(
        self, element: Multiplication, args
    ) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitDivision(self, element: Division, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitNot(self, element: Neg, args) -> npt.NDArray[np.float_]:
        child = self.visit(element.children[0])
        return -1 * child

    def visitAnd(self, element: Conjunction, args) -> npt.NDArray[np.float_]:
        rob = np.full(self.trace_len, np.inf)
        for child in element.children:
            child_rob = self.visit(child)
            rob = np.minimum(child_rob, rob)
        return rob

    def visitOr(self, element: Disjunction, args) -> npt.NDArray[np.float_]:
        rob = np.full(self.trace_len, -np.inf)
        for child in element.children:
            child_rob = self.visit(child)
            rob = np.maximum(child_rob, rob)
        return rob

    def visitImplies(self, element: Implies, args) -> npt.NDArray[np.float_]:
        left_child = -1 * self.visit(element.children[0])
        right_child = self.visit(element.children[1])
        return np.maximum(left_child, right_child)

    def visitIff(self, element: Iff, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError()

    def visitXor(self, element: Xor, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError()

    def visitEventually(self, element: Eventually, args) -> npt.NDArray[np.float_]:
        child = self.visit(element.children[0])
        rob = np.copy(child)
        for i in reversed(range(len(child))):
            if i == 0:
                # Skip last element
                continue
            idx = -i - 1
            rob[idx] = max(child[idx], rob[idx + 1])

        return rob

    def visitAlways(self, element: Always, args) -> npt.NDArray[np.float_]:
        child = self.visit(element.children[0])
        rob = np.copy(child)
        for i in range(len(child)):
            if i == 0:
                # Skip last element
                continue
            idx = -i - 1
            rob[idx] = min(child[idx], rob[idx + 1])

        return rob

    def visitUntil(self, element: Until, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError()

    def visitOnce(self, element: Once, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitHistorically(self, element: Historically, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitSince(self, element: Since, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitRise(self, element: Rise, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitFall(self, element: Fall, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitConstant(self, element: Constant, args) -> npt.NDArray[np.float_]:
        return np.full(self.trace_len, element.val)

    def visitPrevious(self, element: Previous, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitNext(self, element: Next, args) -> npt.NDArray[np.float_]:
        child = self.visit(element.children[0])
        rob = np.copy(child)
        for i in range(len(child)):
            if i == 0:
                continue
            idx = -i - 1
            rob[idx] = child[idx + 1]
        return rob

    def visitTimedPrecedes(
        self, element: TimedPrecedes, args
    ) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedOnce(self, element: TimedOnce, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedHistorically(
        self, element: TimedHistorically, args
    ) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedSince(self, element: TimedSince, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedAlways(self, element: TimedAlways, args) -> npt.NDArray[np.float_]:
        child = self.visit(element.children[0])
        start, end = element.begin, element.end
        _, rob = np.asarray(supermaxmin(child[start:], end - start))
        return rob

    def visitTimedEventually(
        self, element: TimedEventually, args
    ) -> npt.NDArray[np.float_]:
        child = self.visit(element.children[0])
        start, end = element.begin, element.end
        rob, _ = np.asarray(supermaxmin(child[start:], end - start))
        return rob

    def visitTimedUntil(self, element: TimedUntil, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitDefault(self, element, args) -> npt.NDArray[np.float_]:
        raise NotImplementedError(NOT_IMPLEMENTED)


def compute_robustness(
    trace: Mapping[str, Sequence[Union[int, float]]], spec: AbstractNode
) -> float:
    return _FastRobustness(trace).compute(spec)
