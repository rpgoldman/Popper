import abc
from collections import defaultdict
from typing import Set, TYPE_CHECKING, List, Optional, Sequence, Tuple, Callable, Dict, Iterator

import clingo

from .type_defs import Literal, RuleBase, Rule

if TYPE_CHECKING:
    from .util import Settings

class Generator(abc.ABC):
    settings: "Settings"
    solver: clingo.Control
    handle: Optional[Iterator[clingo.Model]]
    clingo_handle: Optional[clingo.solving.SolveHandle]
    model: Optional[clingo.Model]
    cached_clingo_atoms: Dict[int, clingo.Symbol] # hash of literal to clingo Symbol

    def set_handle(self, reset: bool = False) -> None:
        """
        Reset the Generator's paired Clingo handles.
        Parameters
        ----------
        reset: bool, optional
           Whether to reset the handles (i.e., reset the search).  If true,
           then make new `handle` and `clingo_handle` for the generator.
           Otherwise (the default), only make new handles if the handles
           are not already set.
        """
        # NOTE: Not sure whether this should reset self.model when
        # resetting the handles
        if self.handle is None or reset:
            clingo_handle = self.solver.solve(yield_=True)
            self.clingo_handle = clingo_handle
            self.handle = iter(clingo_handle)
        else:
            assert self.clingo_handle is not None, \
                "This generator's model iterator is bound, but not the corresponding clingo handle."

    def __init__(self, settings: "Settings") -> None:
        self.savings = 0
        self.settings = settings
        self.cached_clingo_atoms = {}
        self.handle = None
        self.clingo_handle = None
        self.model = None

    @abc.abstractmethod
    def get_prog(self) -> Optional[RuleBase]:
        pass

    # @abc.abstractmethod
    # def gen_symbol(self, literal, backend):
    #     pass

    @abc.abstractmethod
    def update_solver(self, size):
        pass

    # @abc.abstractmethod
    # def update_number_of_literals(self, size):
    #     pass

    # @abc.abstractmethod
    # def update_number_of_vars(self, size):
    #     pass

    # @abc.abstractmethod
    # def update_number_of_rules(self, size):
    #     pass

    @abc.abstractmethod
    def prune_size(self, size):
        pass

    # @abc.abstractmethod
    # def get_ground_rules(self, rule):
    #     pass

    # @abc.abstractmethod
    # def parse_handles(self, new_handles):
    #     pass

    @abc.abstractmethod
    def constrain(self, tmp_new_cons):
        pass

    @abc.abstractmethod
    def build_encoding(self, bkcons: List, settings: "Settings") -> str:
        """Build and return a string for an ASP solver."""

    @abc.abstractmethod
    def init_solver(self, encoding: str) -> clingo.Control:
        """Incorporate the `encoding` into a new solver and return it."""

    def parse_model_pi(self, model: Sequence[clingo.Symbol]) -> RuleBase:
        settings = self.settings
        # directions = defaultdict(lambda: defaultdict(lambda: '?'))
        rule_index_to_body = defaultdict(set)
        rule_index_to_head = {}
        # rule_index_ordering = defaultdict(set)

        for atom in model:
            args = atom.arguments
            name = atom.name

            if name == "body_literal":
                rule_index = args[0].number
                predicate = args[1].name
                atom_args = args[3].arguments
                atom_args = settings.cached_atom_args[tuple(atom_args)]
                arity = len(atom_args)
                body_literal = (predicate, atom_args, arity)
                rule_index_to_body[rule_index].add(body_literal)

            elif name == "head_literal":
                rule_index = args[0].number
                predicate = args[1].name
                atom_args = args[3].arguments
                atom_args = settings.cached_atom_args[tuple(atom_args)]
                arity = len(atom_args)
                head_literal = (predicate, atom_args, arity)
                rule_index_to_head[rule_index] = head_literal

        prog = []

        for rule_index in rule_index_to_head:  # pylint: disable=C0206
            head_pred, head_args, _head_arity = rule_index_to_head[rule_index]
            head = Literal(head_pred, head_args)
            body: Set[Literal] = set()
            for body_pred, body_args, _body_arity in rule_index_to_body[rule_index]:
                body.add(Literal(body_pred, body_args))
            rule = head, frozenset(body)
            prog.append(rule)

        return frozenset(prog)

    @staticmethod
    def arg_to_symbol(arg):
        if isinstance(arg, tuple):
            return clingo.Tuple_(tuple(Generator.arg_to_symbol(a) for a in arg))
        if isinstance(arg, int):
            return clingo.Number(arg)
        if isinstance(arg, str):
            return clingo.Function(arg)
        raise TypeError(f"Cannot translate {arg} to clingo Symbol")

    @staticmethod
    def atom_to_symbol(pred, args):
        xs = tuple(Generator.arg_to_symbol(arg) for arg in args)
        return clingo.Function(name=pred, arguments=xs)

    def parse_model_single_rule(self, model: Sequence[clingo.Symbol]) -> RuleBase:
        settings = self.settings
        head: Literal = settings.head_literal
        body: Set[Literal] = set()
        for atom in model:
            args = atom.arguments
            predicate = args[1].name
            atom_args = tuple(args[3].arguments)
            literal: Literal = settings.retrieve_literal(predicate, atom_args)
            body.add(literal)
        rule: Rule = head, frozenset(body)
        return frozenset([rule])

    def parse_model_recursion(self, model: Sequence[clingo.Symbol]) -> RuleBase:
        settings = self.settings
        rule_index_to_body = defaultdict(set)
        head = settings.head_literal

        for atom in model:
            args = atom.arguments
            rule_index = args[0].number
            predicate = args[1].name
            atom_args = tuple(args[3].arguments)
            literal = settings.retrieve_literal(predicate, atom_args)
            rule_index_to_body[rule_index].add(literal)

        prog = []
        for rule_index, body in rule_index_to_body.items():
            fbody = frozenset(body)
            rule = head, fbody
            prog.append(rule)

        return frozenset(prog)

    def instantiate_constraints(self, new_ground_cons):
        tmp: Callable[[List[Tuple[clingo.Symbol, bool]]], None] = self.model.context.add_nogood
        cached_clingo_atoms = self.cached_clingo_atoms
        for ground_body in new_ground_cons:
            nogood = []
            for sign, pred, args in ground_body:
                k = hash((sign, pred, args))
                try:
                    x = cached_clingo_atoms[k]
                except KeyError:
                    x = (Generator.atom_to_symbol(pred, args), sign)
                    cached_clingo_atoms[k] = x
                nogood.append(x)
            tmp(nogood)
