import copy
from typing import Callable, Generic, Mapping, TypeVar, Union

from syma.automaton import SymbolicAutomaton
from syma.constraint.constraint import Constraint
from syma.constraint.node import (EQ, GEQ, GT, LEQ, LT, NEQ, And, BoolConst,
                                  BoolVar, IntConst, IntVar, Node, NodeVisitor,
                                  Not, Or, RealConst, RealVar)
from syma_arv.semiring import Semiring

Value = Union[bool, int, float]
Values = Mapping[str, Value]
DistanceFn = Callable[[Value, Value], Value]


class ValueGuardDistance(NodeVisitor):
    def __init__(self, semiring: Semiring, distance_fn: DistanceFn):
        self._ops = semiring
        self._dist = distance_fn

    def __call__(self, values: Values, guard: Constraint) -> Value:
        dist = self.visit(guard.formula, values)
        return dist

    def visitBoolConst(self, node: BoolConst, _: Values) -> Value:
        if node.value:
            return self._ops.e_times
        return self._ops.e_plus

    def visitIntConst(self, node: IntConst, _: Values) -> Value:
        return int(node.value)

    def visitRealConst(self, node: RealConst, _: Values) -> Value:
        return node.value

    def visitBoolVar(self, node: BoolVar, values: Values) -> Value:
        return bool(values[node.name])

    def visitIntVar(self, node: IntVar, values: Values) -> Value:
        return int(values[node.name])

    def visitRealVar(self, node: RealVar, values: Values) -> Value:
        return float(values[node.name])

    def visitGEQ(self, node: GEQ, values: Values) -> Value:
        lhs = self.visit(node.children[0], values)
        rhs = self.visit(node.children[1], values)
        if lhs >= rhs:
            return self._ops.e_times
        return self._dist(lhs, rhs)

    def visitGT(self, node: GT, values: Values) -> Value:
        lhs = self.visit(node.children[0], values)
        rhs = self.visit(node.children[1], values)
        if lhs > rhs:
            return self._ops.e_times
        return self._dist(lhs, rhs)

    def visitLEQ(self, node: LEQ, values: Values) -> Value:
        lhs = self.visit(node.children[0], values)
        rhs = self.visit(node.children[1], values)
        if lhs <= rhs:
            return self._ops.e_times
        return self._dist(lhs, rhs)

    def visitLT(self, node: LT, values: Values) -> Value:
        lhs = self.visit(node.children[0], values)
        rhs = self.visit(node.children[1], values)
        if lhs < rhs:
            return self._ops.e_times
        return self._dist(lhs, rhs)

    def visitEQ(self, node: EQ, values: Values) -> Value:
        lhs = self.visit(node.children[0], values)
        rhs = self.visit(node.children[1], values)
        if lhs == rhs:
            return self._ops.e_times
        return self._dist(lhs, rhs)

    def visitNEQ(self, node: NEQ, values: Values) -> Value:
        lhs = self.visit(node.children[0], values)
        rhs = self.visit(node.children[1], values)
        if lhs != rhs:
            return self._ops.e_times
        return self._dist(lhs, rhs)

    def visitNot(self, node: Not, values: Values) -> Value:
        raise ValueError("Expression needs to be in DNF. `Not` should not exist")

    def visitAnd(self, node: And, values: Values) -> Value:
        lhs = self.visit(node.children[0], values)
        rhs = self.visit(node.children[1], values)
        return self._ops.times(lhs, rhs)

    def visitOr(self, node: Or, values: Values) -> Value:
        lhs = self.visit(node.children[0], values)
        rhs = self.visit(node.children[1], values)
        return self._ops.plus(lhs, rhs)


class Monitor(object):
    def __init__(
        self,
        automaton: SymbolicAutomaton,
        semiring: Semiring,
        distance_fn: DistanceFn,
    ):
        self._aut = automaton
        self._op = semiring
        self._dist = distance_fn
        self._vpd = ValueGuardDistance(semiring, distance_fn)

        # Initialize the cost table
        self._cost = dict()  # type: dict[int, Value]
        self._cost_p = self._op.zero
        self._cost_m = self._op.zero
        self.reset()

    def reset(self):
        for q in self._aut.locations:
            info = self._aut[q]
            if info.initial:
                self._cost[q] = self._op.e_times
            else:
                self._cost[q] = self._op.e_plus

        self._update_robustness()

    def _update_robustness(self):
        self._cost_p = self._op.zero
        self._cost_m = self._op.zero
        for q in self._aut.locations:
            info = self._aut[q]
            if info.accepting:
                self._cost_p = self._op.plus(self._cost_p, self._cost[q])
            else:
                self._cost_m = self._op.plus(self._cost_m, self._cost[q])

    @property
    def robustness(self):
        if self._cost_p == 0:
            return -self._cost_m
        return self._cost_p

    def update(self, values: Values):
        new_cost = self._cost.copy()
        for q in self._aut.locations:
            val = self._op.e_plus
            for q_ in self._aut._graph.predecessors(q):
                prev_cost = self._cost[q_]
                guard = self._aut.get_guard(q_, q)
                vpd = self._vpd(values, guard)
                val = self._op.plus(val, self._op.times(prev_cost, vpd))
            new_cost[q] = val

        self._cost = new_cost
        self._update_robustness()
