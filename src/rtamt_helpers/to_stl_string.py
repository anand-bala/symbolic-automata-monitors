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


class _ToStlString(STLVisitor):
    def visit(self, spec: AbstractNode) -> str:
        return super().visit(spec, ())

    def visitPredicate(self, element: Predicate, args) -> str:
        lhs, rhs = self.visit(element.children[0]), self.visit(element.children[1])
        op = StlComparisonOperator(element.operator)

        if op == StlComparisonOperator.LEQ:
            op_str = "<="
        elif op == StlComparisonOperator.LESS:
            op_str = "<"
        elif op == StlComparisonOperator.GEQ:
            op_str = ">="
        elif op == StlComparisonOperator.GREATER:
            op_str = ">"
        elif op == StlComparisonOperator.EQUAL:
            op_str = "=="
        elif op == StlComparisonOperator.NEQ:
            op_str = "!="
        else:
            raise ValueError(f"No idea what operation this is: {op}")

        return f"({lhs} {op_str} {rhs})"

    def visitVariable(self, element: Variable, args):
        return element.var

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

    def visitNot(self, element: Neg, args) -> str:
        child_str = self.visit(element.children[0])
        return f"! {child_str}"

    def visitAnd(self, element: Conjunction, args):
        children = [f"{self.visit(child)}" for child in element.children]
        return "(" + " & ".join(children) + ")"

    def visitOr(self, element: Disjunction, args):
        children = [f"({self.visit(child)})" for child in element.children]
        return "(" + " | ".join(children) + ")"

    def visitImplies(self, element: Implies, args):
        left_child = self.visit(element.children[0])
        right_child = self.visit(element.children[1])
        return f"( !{left_child} | {right_child} )"

    def visitIff(self, element: Iff, args):
        left_child = self.visit(element.children[0])
        right_child = self.visit(element.children[1])
        return f"( ( {left_child} & {right_child} ) | ( ! {left_child} & ! {right_child} ) )"

    def visitXor(self, element: Xor, args):
        left_child = self.visit(element.children[0])
        right_child = self.visit(element.children[1])
        return f"( ( {left_child} & ! {right_child} ) | ( ! {left_child} & {right_child} ) )"

    def visitEventually(self, element: Eventually, args):
        child = self.visit(element.children[0])
        return f"( F {child} )"

    def visitAlways(self, element: Always, args):
        child = self.visit(element.children[0])
        return f"( G {child} )"

    def visitUntil(self, element: Until, args):
        left = self.visit(element.children[0])
        right = self.visit(element.children[1])

        return f"( {left} U {right} )"

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

    def visitConstant(self, element: Constant, args):
        return str(element.val)

    def visitPrevious(self, element: Previous, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitNext(self, element: Next, args):
        child = self.visit(element.children[0])
        return f"( X {child} )"

    def visitTimedPrecedes(self, element: TimedPrecedes, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedOnce(self, element: TimedOnce, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedHistorically(self, element: TimedHistorically, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedSince(self, element: TimedSince, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitTimedAlways(self, element: TimedAlways, args):
        child = self.visit(element.children[0])
        start, end = element.begin, element.end
        return f"( G[{start},{end}] {child} )"

    def visitTimedEventually(self, element: TimedEventually, args):
        child = self.visit(element.children[0])
        start, end = element.begin, element.end
        return f"( F[{start},{end}] {child} )"

    def visitTimedUntil(self, element: TimedUntil, args):
        raise NotImplementedError(NOT_IMPLEMENTED)

    def visitDefault(self, element, args):
        raise NotImplementedError(NOT_IMPLEMENTED)


def to_stl_string(spec: AbstractNode) -> str:
    return _ToStlString().visit(spec)
