"""Convert predicates to Z3 formula"""

from typing import Dict, Union

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
from rtamt.node.ltl.once import Once
from rtamt.node.ltl.predicate import Predicate
from rtamt.node.ltl.previous import Previous
from rtamt.node.ltl.rise import Rise
from rtamt.node.ltl.since import Since
from rtamt.node.ltl.until import Until
from rtamt.node.ltl.variable import Variable
from rtamt.node.ltl.xor import Xor
from rtamt.node.stl.timed_always import TimedAlways
from rtamt.node.stl.timed_until import TimedUntil
from rtamt.spec.stl.discrete_time.comp_op import StlComparisonOperator
from rtamt.spec.stl.discrete_time.visitor import STLVisitor

import syma.constraint.node as sym_node

NOT_IMPLEMENTED = "You should implement this."


class ToConstraint(STLVisitor):
    def __init__(self, var_type_dict: Dict[str, str]):
        super().__init__()
        self.var_type_dict = var_type_dict

    def convert(self, spec: Union[STLSpecification, AbstractNode]) -> sym_node.Node:
        formula = self.visit(spec, ())
        return formula

    def visitPredicate(self, element: Predicate, args) -> sym_node.Node:
        lhs = self.visit(element.children[0], args)
        rhs = self.visit(element.children[1], args)

        if element.operator == StlComparisonOperator.GEQ:
            return lhs >= rhs
        if element.operator == StlComparisonOperator.LEQ:
            return lhs <= rhs
        if element.operator == StlComparisonOperator.GREATER:
            return lhs > rhs
        if element.operator == StlComparisonOperator.LESS:
            return lhs < rhs
        if element.operator == StlComparisonOperator.EQUAL:
            return lhs == rhs
        if element.operator == StlComparisonOperator.NEQ:
            return lhs != rhs

        raise RuntimeError("This shouldn't happen")

    def visitVariable(self, element: Variable, _) -> sym_node.Node:
        var_name = element.name  # type: str
        var_type = self.var_type_dict[var_name]
        if var_type == "int":
            return sym_node.IntVar(var_name)
        if var_type == "float":
            return sym_node.RealVar(var_name)
        if var_type == "bool":
            return sym_node.BoolVar(var_name)
        raise NotImplementedError(f"Unsupported type {var_type}")

    def visitConstant(self, element: Constant, args):
        return sym_node.Constant(element.val)

    def visitAbs(self, element: Abs, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitSqrt(self, element: Sqrt, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitPow(self, element: Pow, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitExp(self, element: Exp, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitAddition(self, element: Addition, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitSubtraction(self, element: Subtraction, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitMultiplication(self, element: Multiplication, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitDivision(self, element: Division, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitNot(self, element: Neg, args) -> sym_node.Node:
        child = self.visit(element.children[0], args)
        return sym_node.Not(child)

    def visitAnd(self, element: Conjunction, args):
        children = [self.visit(child, args) for child in element.children]
        return sym_node.And(*children)

    def visitOr(self, element: Disjunction, args):
        children = [self.visit(child, args) for child in element.children]
        return sym_node.Or(*children)

    def visitImplies(self, element: Implies, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitIff(self, element: Iff, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitXor(self, element: Xor, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitEventually(self, element: Eventually, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitAlways(self, element: Always, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitUntil(self, element: Until, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitOnce(self, element: Once, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitHistorically(self, element: Historically, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitSince(self, element: Since, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitRise(self, element: Rise, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitFall(self, element: Fall, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitPrevious(self, element: Previous, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitNext(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedPrecedes(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedOnce(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedHistorically(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedSince(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedAlways(self, element: TimedAlways, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedEventually(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedUntil(self, element: TimedUntil, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitDefault(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)


def from_node_to_constraint(
    spec: AbstractNode, var_type_dict: Dict[str, str]
) -> sym_node.Node:
    return ToConstraint(var_type_dict).convert(spec)


def to_constraint(spec: STLSpecification) -> sym_node.Node:
    return from_node_to_constraint(spec.top, spec.var_type_dict)
