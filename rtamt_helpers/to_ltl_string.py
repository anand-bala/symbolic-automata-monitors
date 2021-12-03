import itertools
import string
from typing import Dict, Tuple

from rtamt import STLSpecification
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


class ToLtlString(STLVisitor):
    """Convert an STL formula to a an LTL formula.

    1. Any predicate (symbolic) is assigned a label and stored in a map.
    2. Any Bounded Temporal Operator is converted to a sequence of nexted Next
       operations.
    """

    def __init__(self):
        super().__init__()

        self.predicate_map = dict()  # type: Dict[str, AbstractNode]

        self._label_prefix = "pred_"
        self._label_gen = itertools.product(
            string.digits,
            string.ascii_lowercase,
        )

    def _next_label(self) -> str:
        """Should pring a0, b0, c0, ..."""
        return self._label_prefix + "".join(reversed(next(self._label_gen)))

    def convert(self, spec: STLSpecification) -> Tuple[str, Dict[str, AbstractNode]]:
        formula = self.visit(spec, ())
        return formula, self.predicate_map

    def visitPredicate(self, element: Predicate, _) -> str:
        label = self._next_label()
        self.predicate_map[label] = element
        return label

    def visitVariable(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitAbs(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitSqrt(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitPow(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitExp(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitAddition(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitSubtraction(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitMultiplication(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitDivision(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitNot(self, element: Neg, args) -> str:
        child_str = self.visit(element.children[0], args)
        return f"! {child_str}"

    def visitAnd(self, element: Conjunction, args):
        children = [f"{self.visit(child, args)}" for child in element.children]
        return "(" + " & ".join(children) + ")"

    def visitOr(self, element: Disjunction, args):
        children = [f"({self.visit(child, args)})" for child in element.children]
        return "(" + " | ".join(children) + ")"

    def visitImplies(self, element: Implies, args):
        left_child = self.visit(element.children[0], args)
        right_child = self.visit(element.children[1], args)
        return f"( !{left_child} | {right_child} )"

    def visitIff(self, element: Iff, args):
        left_child = self.visit(element.children[0], args)
        right_child = self.visit(element.children[1], args)
        return f"( ( {left_child} & {right_child} ) | ( ! {left_child} & ! {right_child} ) )"

    def visitXor(self, element: Xor, args):
        left_child = self.visit(element.children[0], args)
        right_child = self.visit(element.children[1], args)
        return f"( ( {left_child} & ! {right_child} ) | ( ! {left_child} & {right_child} ) )"

    def visitEventually(self, element: Eventually, args):
        child = self.visit(element.children[0], args)
        return f"( F {child} )"

    def visitAlways(self, element, args):
        child = self.visit(element.children[0], args)
        return f"( G {child} )"

    def visitUntil(self, element, args):
        left = self.visit(element.children[0], args)
        right = self.visit(element.children[1], args)

        return f"( {left} U {right} )"

    def visitOnce(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitHistorically(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitSince(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitRise(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitFall(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitConstant(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitPrevious(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitNext(self, element, args):
        child = self.visit(element.children[0], args)
        return f"( X {child} )"

    def visitTimedPrecedes(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedOnce(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedHistorically(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedSince(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedAlways(self, element: TimedAlways, args):
        child = self.visit(element.children[0], args)
        length = element.end - element.begin
        assert isinstance(length, int)

        formula = str(child)  # len = 0
        for _ in range(length):  # len = 1..length
            formula = f"{child} & X ({formula})"

        for _ in range(element.begin):  # if begin > 0
            formula = f"X({formula})"

        return formula

    def visitTimedEventually(self, element, args):
        child = self.visit(element.children[0], args)
        length = element.end - element.begin
        assert isinstance(length, int)

        formula = str(child)  # len = 0
        for _ in range(length):  # len = 1..length
            formula = f"({child} | X {formula})"

        for _ in range(element.begin):  # if begin > 0
            formula = f"X({formula})"

        return formula

    def visitTimedUntil(self, element: TimedUntil, args):
        """
        Here we use the decomposition used in [donze2013efficient]_.

        .. [donze2013efficient] A. Donzé, T. Ferrère, and O. Maler,
           "Efficient Robust Monitoring for STL,"
           in Computer Aided Verification, Berlin, Heidelberg, 2013, pp. 264–279.
           doi: 10.1007/978-3-642-39799-8_19.

        Essentially,

            p U[a, b] q  <=>  (F[a, b] q) & (p U[a, inf) q)

        and

            p U[a, inf)  <=>  G[0,a] (p U q)
        """
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitDefault(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)


def to_ltl_string(spec: STLSpecification) -> Tuple[str, Dict[str, AbstractNode]]:
    return ToLtlString().convert(spec)
