from functools import reduce

from syma.constraint.node import (
    EQ,
    GEQ,
    GT,
    LEQ,
    LT,
    NEQ,
    And,
    BoolConst,
    BoolVar,
    IntConst,
    IntVar,
    Node,
    NodeType,
    NodeVisitor,
    Not,
    Or,
    RealConst,
    RealVar,
)


class ToNNF(NodeVisitor[Node]):
    """Convert a given formula to NNF"""

    def __init__(self, formula: Node):
        self.formula = formula

    def translate(self) -> Node:
        return self.visit(self.formula, negate=False)

    def visitIntConst(self, _: IntConst) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit IntConst")

    def visitRealConst(self, _: RealConst) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit RealConst")

    def visitIntVar(self, _: IntVar) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit IntVar")

    def visitRealVar(self, _: RealVar) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit RealVar")

    def visitBoolConst(self, node: BoolConst, *, negate: bool) -> Node:
        if negate:
            return BoolConst(not node.value)
        return node

    def visitBoolVar(self, node: BoolVar, *, negate: bool) -> Node:
        if negate:
            return Not(node)
        return node

    def visitEQ(self, node: EQ, *, negate: bool) -> Node:
        if negate:
            return NEQ(node.children[0], node.children[1]).make_canonical()
        return node.make_canonical()

    def visitNEQ(self, node: NEQ, *, negate: bool) -> Node:
        if negate:
            return EQ(node.children[0], node.children[1]).make_canonical()
        return node.make_canonical()

    def visitGEQ(self, node: GEQ, *, negate: bool) -> Node:
        if negate:
            return LT(node.children[0], node.children[1]).make_canonical()
        return node.make_canonical()

    def visitGT(self, node: GT, *, negate: bool) -> Node:
        if negate:
            return LEQ(node.children[0], node.children[1]).make_canonical()
        return node.make_canonical()

    def visitLEQ(self, node: LEQ, *, negate: bool) -> Node:
        if negate:
            return GT(node.children[0], node.children[1]).make_canonical()
        return node.make_canonical()

    def visitLT(self, node: LT, *, negate: bool) -> Node:
        if negate:
            return GEQ(node.children[0], node.children[1]).make_canonical()
        return node.make_canonical()

    def visitAnd(self, node: And, *, negate: bool) -> Node:
        if not negate:
            ops = [self.visit(child, negate=False) for child in node.children]
            return And(*ops)
        # DeMorgan's law
        ops = [self.visit(child, negate=True) for child in node.children]
        return Or(*ops)

    def visitOr(self, node: Or, *, negate: bool) -> Node:
        if not negate:
            ops = [self.visit(child, negate=False) for child in node.children]
            return Or(*ops)
        # DeMorgan's law
        ops = [self.visit(child, negate=True) for child in node.children]
        return And(*ops)

    def visitNot(self, node: Not, *, negate: bool) -> Node:
        child = node.children[0]

        if negate:
            # This is a not(not(child)) situation
            # So we return the converted child
            return self.visit(child, negate=False)

        # Now, we just need to negate the child.
        return self.visit(child, negate=True)


def to_nnf(formula: Node) -> Node:
    return ToNNF(formula).translate()


class ToDNF(NodeVisitor[Node]):
    """Convert a given formula to DNF"""

    def __init__(self, formula: Node):
        # First translate to NNF
        self.formula = to_nnf(formula)

    def translate(self) -> Node:
        return self.visit(self.formula)

    def visitIntConst(self, _: IntConst) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit IntConst")

    def visitRealConst(self, _: RealConst) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit RealConst")

    def visitIntVar(self, _: IntVar) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit IntVar")

    def visitRealVar(self, _: RealVar) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit RealVar")

    def visitBoolConst(self, node: BoolConst) -> Node:
        return node

    def visitBoolVar(self, node: BoolVar) -> Node:
        return node

    def visitEQ(self, node: EQ) -> Node:
        return node

    def visitNEQ(self, node: NEQ) -> Node:
        return node

    def visitGEQ(self, node: GEQ) -> Node:
        return node

    def visitGT(self, node: GT) -> Node:
        return node

    def visitLEQ(self, node: LEQ) -> Node:
        return node

    def visitLT(self, node: LT) -> Node:
        return node

    def visitNot(self, node: Not) -> Node:
        # Assuming NNF, the Not should only be at the BoolVars.
        return node

    def visitOr(self, node: Or) -> Node:
        # We don't have to do much.
        # Just apply the transform to the children, which should output them in DNF.
        disjunction = [self.visit(child) for child in node.children]
        if len(disjunction) == 0:
            return BoolConst(False)
        if len(disjunction) == 1:
            return disjunction[0]

        return Or(*disjunction)

    def _distributeAnd(self, a: Node, b: Node) -> Node:
        """Given two DNF formulas, convert `a & b` to DNF."""
        if (a.node_type != NodeType.Or) and (b.node_type != NodeType.Or):
            # Since a and b are DNF, if they are not Or, they must be atomic or And.
            # Thus, this is a NOP.
            return a & b
        elif a.node_type != NodeType.Or:
            # Make sure `a` is an Or expression.
            a, b = b, a

        # Let `a = (p | q)`
        # Recursively distribute as `(p | q) & b = (p & b) | (q & b)`
        # Since `p`, `q`, and `b` are DNF, the precondition for _distributeAnd
        # recursively applies.
        distributed_ops = [self._distributeAnd(p, b) for p in a.children]
        # Post condition: List[Or]
        return reduce(lambda x, y: x | y, distributed_ops)

    def visitAnd(self, node: And) -> Node:

        # We need to distribute the AND over the ORs.
        # First, apply the transform to the children.
        children = [self.visit(child) for child in node.children]

        # Now, we do a pairwise distribution of each And into any Or sub-expression.
        return reduce(self._distributeAnd, children)


def to_dnf(formula: Node) -> Node:
    return ToDNF(formula).translate()


class ToCNF(NodeVisitor[Node]):
    """Convert a given formula to CNF"""

    def __init__(self, formula: Node):
        self.formula = formula

    def translate(self) -> Node:
        # First translate to NNF
        self.formula = to_nnf(self.formula)
        return self.visit(self.formula)

    def visitIntConst(self, _: IntConst) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit IntConst")

    def visitRealConst(self, _: RealConst) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit RealConst")

    def visitIntVar(self, _: IntVar) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit IntVar")

    def visitRealVar(self, _: RealVar) -> Node:
        raise RuntimeError("The NNF converter shouldn't visit RealVar")

    def visitBoolConst(self, node: BoolConst) -> Node:
        return node

    def visitBoolVar(self, node: BoolVar) -> Node:
        return node

    def visitEQ(self, node: EQ) -> Node:
        return node

    def visitNEQ(self, node: NEQ) -> Node:
        return node

    def visitGEQ(self, node: GEQ) -> Node:
        return node

    def visitGT(self, node: GT) -> Node:
        return node

    def visitLEQ(self, node: LEQ) -> Node:
        return node

    def visitLT(self, node: LT) -> Node:
        return node

    def visitNot(self, node: Not) -> Node:
        # Assuming NNF, the Not should only be at the BoolVars.
        return node

    def visitAnd(self, node: And) -> Node:
        # We don't have to do much.
        # Just apply the transform to the children, which should output them in CNF.
        expr = node.children[0]
        for child in node.children[1:]:
            expr = expr | child

        return expr

    def _distributeOr(self, a: Node, b: Node) -> Node:
        """Given two CNF formulas, convert `a | b` to CNF."""
        if (a.node_type != NodeType.And) and (b.node_type != NodeType.And):
            # Since a and b are CNF, if they are not And, they must be atomic or Or.
            # Else one of them is a compound expression
            #
            # Thus, this is a NOP.
            return a | b
        elif a.node_type != NodeType.And:
            # Make sure `a` is an And expression.
            a, b = b, a

        # Let `a = (p & q)`
        # Recursively distribute as `(p & q) | b = (p | b) & (q | b)`
        # Since `p`, `q`, and `b` are CNF, the precondition for _distributeOr
        # recursively applies.
        distributed_ops = [self._distributeOr(p, b) for p in a.children]
        # Post condition: List[And]
        return reduce(lambda x, y: x & y, distributed_ops)

    def visitOr(self, node: Or) -> Node:

        # We need to distribute the ORs over the ANDs.
        # First, apply the transform to the children.
        children = [self.visit(child) for child in node.children]

        # Now, we do a pairwise distribution of each Or into any And sub-expression.
        return reduce(self._distributeOr, children)


def to_cnf(formula: Node) -> Node:
    return ToCNF(formula).translate()
