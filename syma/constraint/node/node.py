from __future__ import annotations

from typing import List, Union


class Node(object):
    def __init__(self):
        self.children: List["Node"] = list()

    def add_child(self, child: "Node"):
        self.children.append(child)

    def __lt__(self, other: "Node") -> "LT":
        return LT(self, other)

    def __le__(self, other: "Node") -> "LEQ":
        return LEQ(self, other)

    def __gt__(self, other: "Node") -> "GT":
        return GT(self, other)

    def __ge__(self, other: "Node") -> "GEQ":
        return GEQ(self, other)

    def __invert__(self) -> "Not":
        return Not(self)

    def __or__(self, other: "Node") -> "Or":
        return Or(self, other)

    def __and__(self, other: "Node") -> "And":
        return And(self, other)


class BoolConst(Node):
    def __init__(self, value: bool):
        super().__init__()
        self._value = value

    @property
    def value(self) -> bool:
        return self._value

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


class LEQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) <= ({str(self.children[1])})"

    def __repr__(self):
        return f"LEQ(\n\t{str(self.children[0])}, \n\t{str(self.children[1])})"


class LT(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) < ({str(self.children[1])})"

    def __repr__(self):
        return f"LT(\n\t{str(self.children[0])}, \n\t{str(self.children[1])})"


class GEQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) >= ({str(self.children[1])})"

    def __repr__(self):
        return f"GEQ(\n\t{str(self.children[0])}, \n\t{str(self.children[1])})"


class GT(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) > ({str(self.children[1])})"

    def __repr__(self):
        return f"GT(\n\t{str(self.children[0])}, \n\t{str(self.children[1])})"


class EQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) == ({str(self.children[1])})"

    def __repr__(self):
        return f"EQ(\n\t{str(self.children[0])}, \n\t{str(self.children[1])})"


class NEQ(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) != ({str(self.children[1])})"

    def __repr__(self):
        return f"NEQ(\n\t{str(self.children[0])}, \n\t{str(self.children[1])})"


class Not(Node):
    def __init__(self, op: Node):
        Node.__init__(self)
        self.children.append(op)

    def __str__(self):
        return f"not ({str(self.children[0])})"

    def __repr__(self):
        return f"Not({str(self.children[0])})"


class And(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) and ({str(self.children[1])})"

    def __repr__(self):
        return f"And({str(self.children[0])}, {str(self.children[1])})"


class Or(Node):
    def __init__(self, op1: Node, op2: Node):
        Node.__init__(self)
        self.children.append(op1)
        self.children.append(op2)

    def __str__(self):
        return f"({str(self.children[0])}) or ({str(self.children[1])})"

    def __repr__(self):
        return f"Or({str(self.children[0])}, {str(self.children[1])})"
