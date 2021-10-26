from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, List, Union

if TYPE_CHECKING:
    from syma.constraint.node.visitor import NodeVisitor


class Node(ABC):
    def __init__(self):
        self.children: List["Node"] = list()

    def add_child(self, child: "Node"):
        self.children.append(child)

    def __lt__(self, other: Union["Node", int, float]) -> "LT":
        if isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return LT(self, other)

    def __le__(self, other: Union["Node", int, float]) -> "LEQ":
        if isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return LEQ(self, other)

    def __gt__(self, other: Union["Node", int, float]) -> "GT":
        if isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return GT(self, other)

    def __ge__(self, other: Union["Node", int, float]) -> "GEQ":
        if isinstance(other, int):
            other = IntConst(other)
        elif isinstance(other, float):
            other = RealConst(other)
        return GEQ(self, other)

    def __invert__(self) -> "Not":
        return Not(self)

    def __or__(self, other: Union["Node", bool]) -> "Or":
        if isinstance(other, bool):
            other = BoolConst(other)
        return Or(self, other)

    def __ror__(self, other: Union["Node", bool]) -> "Or":
        if isinstance(other, bool):
            other = BoolConst(other)
        return Or(self, other)

    def __and__(self, other: Union["Node", bool]) -> "And":
        if isinstance(other, bool):
            other = BoolConst(other)
        return And(self, other)

    def __rand__(self, other: Union["Node", bool]) -> "And":
        if isinstance(other, bool):
            other = BoolConst(other)
        return And(self, other)

    @abstractmethod
    def doVisit(self, visitor: "NodeVisitor", *args):
        ...


class BoolConst(Node):
    def __init__(self, value: bool):
        super().__init__()
        self._value = value

    @property
    def value(self) -> bool:
        return self._value

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitBoolConst(self, *args)

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        return f"BoolConst({self.value})"


class IntConst(Node):
    def __init__(self, value: int):
        super().__init__()
        self._value = value

    @property
    def value(self) -> int:
        return self._value

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        return f"IntConst({self.value})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitIntConst(self, *args)


class RealConst(Node):
    def __init__(self, value: float):
        super().__init__()
        self._value = value

    @property
    def value(self) -> float:
        return self._value

    def __str__(self) -> str:
        return str(self.value)

    def __repr__(self) -> str:
        return f"RealConst({self.value})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitRealConst(self, *args)


def Constant(value: Union[bool, int, float]) -> Node:
    if isinstance(value, bool):
        return BoolConst(value)
    if isinstance(value, int):
        return IntConst(value)
    if isinstance(value, float):
        return RealConst(value)
    raise TypeError(f"Unsupported constant type: {type(value)}")


class BoolVar(Node):
    def __init__(self, name: str):
        super().__init__()
        self._name = name

    @property
    def name(self) -> str:
        return self._name

    def __str__(self) -> str:
        return str(self.name)

    def __repr__(self) -> str:
        return f"BoolVar({self.name})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitBoolVar(self, *args)


class IntVar(Node):
    def __init__(self, name: str):
        super().__init__()
        self._name = name

    @property
    def name(self) -> str:
        return self._name

    def __str__(self) -> str:
        return str(self.name)

    def __repr__(self) -> str:
        return f"IntVar({self.name})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitIntVar(self, *args)


class RealVar(Node):
    def __init__(self, name: str):
        super().__init__()
        self._name = name

    @property
    def name(self) -> str:
        return self._name

    def __str__(self) -> str:
        return str(self.name)

    def __repr__(self) -> str:
        return f"RealVar({self.name})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitRealVar(self, *args)


class LEQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"{str(self.children[0])} <= {str(self.children[1])}"

    def __repr__(self):
        return f"LEQ({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitLEQ(self, *args)


class LT(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"{str(self.children[0])} < {str(self.children[1])}"

    def __repr__(self):
        return f"LT({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitLT(self, *args)


class GEQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"{str(self.children[0])} >= {str(self.children[1])}"

    def __repr__(self):
        return f"GEQ({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitGEQ(self, *args)


class GT(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"{str(self.children[0])} > {str(self.children[1])}"

    def __repr__(self):
        return f"GT({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitGT(self, *args)


class EQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"{str(self.children[0])} == {str(self.children[1])}"

    def __repr__(self):
        return f"EQ({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitEQ(self, *args)


class NEQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"{str(self.children[0])}) != ({str(self.children[1])}"

    def __repr__(self):
        return f"NEQ({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitNEQ(self, *args)


class Not(Node):
    def __init__(self, op: Node):
        Node.__init__(self)
        self.children.append(op)

    def __str__(self):
        return f"not ({str(self.children[0])})"

    def __repr__(self):
        return f"Not({str(self.children[0])})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitNot(self, *args)


class And(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) and ({str(self.children[1])})"

    def __repr__(self):
        return f"And({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitAnd(self, *args)


class Or(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) or ({str(self.children[1])})"

    def __repr__(self):
        return f"Or({str(self.children[0])}, {str(self.children[1])})"

    def doVisit(self, visitor: "NodeVisitor", *args):
        return visitor.visitOr(self, *args)
