"""
Compute the horizon for a STL specificaiton
"""
import numpy as np


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
from rtamt.spec.stl.discrete_time.visitor import STLVisitor

NOT_IMPLEMENTED = "You should implement this."


class _ComputeHorizon(STLVisitor):
    def visit(self, element: AbstractNode) -> int:
        return super().visit(element, ())

    def visitPredicate(self, _: Predicate, args) -> int:
        return 0

    def visitVariable(self, _: Variable, args):
        return 0

    def visitAbs(self, _: Abs, args):
        return 0

    def visitSqrt(self, _: Sqrt, args):
        return 0

    def visitPow(self, _: Pow, args):
        return 0

    def visitExp(self, _: Exp, args):
        return 0

    def visitAddition(self, _: Addition, args):
        return 0

    def visitSubtraction(self, _: Subtraction, args):
        return 0

    def visitMultiplication(self, _: Multiplication, args):
        return 0

    def visitDivision(self, _: Division, args):
        return 0

    def visitNot(self, node: Neg, args) -> int:
        child = node.children[0]
        return self.visit(child)

    def visitAnd(self, node: Conjunction, args):
        return max(self.visit(child) for child in node.children)

    def visitOr(self, node: Disjunction, args):
        return max(self.visit(child) for child in node.children)

    def visitImplies(self, _: Implies, args):
        raise NotImplementedError()

    def visitIff(self, _: Iff, args):
        raise NotImplementedError()

    def visitXor(self, _: Xor, args):
        raise NotImplementedError()

    def visitEventually(self, _: Eventually, args):
        return np.inf

    def visitAlways(self, _: Always, args):
        return np.inf

    def visitUntil(self, _: Until, args):
        return np.inf

    def visitOnce(self, _: Once, args):
        return 0

    def visitHistorically(self, _: Historically, args):
        return 0

    def visitSince(self, _: Since, args):
        return 0

    def visitRise(self, _: Rise, args):
        raise NotImplementedError()

    def visitFall(self, _: Fall, args):
        raise NotImplementedError()

    def visitConstant(self, _: Constant, args):
        return 0

    def visitPrevious(self, _: Previous, args):
        return 0

    def visitNext(self, element: Next, args):
        child = self.visit(element.children[0])
        return 1 + child

    def visitTimedPrecedes(self, _: TimedPrecedes, args):
        return 0

    def visitTimedOnce(self, _: TimedOnce, args):
        return 0

    def visitTimedHistorically(self, _: TimedHistorically, args):
        return 0

    def visitTimedSince(self, _: TimedSince, args):
        return 0

    def visitTimedAlways(self, element: TimedAlways, args):
        child = self.visit(element.children[0])
        length = element.end - element.begin
        assert isinstance(length, int)
        return child + element.end

    def visitTimedEventually(self, element: TimedEventually, args):
        child = self.visit(element.children[0])
        length = element.end - element.begin
        assert isinstance(length, int)
        return child + element.end

    def visitTimedUntil(self, element: TimedUntil, args):
        lhs = self.visit(element.children[0])
        rhs = self.visit(element.children[1])

        length = element.end - element.begin
        assert isinstance(length, int)
        return max([lhs + element.end - 1, rhs + element.end])

    def visitDefault(self, _, args):
        return 0


def compute_spec_horizon(spec: AbstractNode) -> int:
    return _ComputeHorizon().visit(spec)
