from typing import FrozenSet, NamedTuple, Tuple, Literal as TypingLiteral
from clingo import Symbol


class Literal(NamedTuple):
    predicate: str
    arguments: Tuple[Symbol, ...]


Rule = Tuple[Literal, FrozenSet[Literal]]
RuleBase = FrozenSet[Rule]

Bit = TypingLiteral[0, 1]
