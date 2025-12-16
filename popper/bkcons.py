import numbers
import sys
import traceback
from collections import defaultdict
from collections.abc import Hashable
from itertools import product, permutations
from typing import cast, Any, Dict, Iterable, Iterator, \
    List, Tuple, TypeVar
import clingo
import clingo.script
from clingo import Function, Number, Tuple_

from .util import suppress_stdout_stderr, Settings
from .type_defs import Bit

T = TypeVar("T", bound=Hashable)

clingo.script.enable_python()

tmp_map: Dict[int, str] = {}
for i in range(1, 20):
    tmp_map[i] = ','.join(f'V{j}' for j in range(i))

arg_lookup = {clingo.Number(i): chr(ord('A') + i)
              for i in range(100)}

TIDY_OUTPUT = """
#defined body_literal/4.
#defined clause_var/2.
#defined var_type/3.
#defined clause/1.
"""


all_myvars: List[str] = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H']


def connected(xs: Iterable[T], ys: Iterable[T]) -> bool:
    """
    Is some member of `ys` in `xs`?
    """
    xs = set(xs)
    for y in ys:
        if y in xs:
            return True
    return False


def uses_in_order(xs: Iterable[str], ys: Iterable[str]) -> bool:
    """
    Are the variables in `xs` union `ys` used in order?
    """
    zs = set(xs) | set(ys)
    for i in all_myvars[:len(zs)]:
        if i not in zs:
            return False
    return True


def build_props(settings: Settings, arities: Iterable[int]) -> Tuple[Any, Any]:

    myvars = all_myvars[:settings.max_vars]

    def make_pairs() -> List[Tuple[Tuple[str, ...], Tuple[str, ...]]]:
        pairs: set[Tuple[Tuple[str, ...], Tuple[str, ...]]] = set()
        for a1 in arities:
            xs: Tuple[str, ...] = tuple(myvars[:a1])
            ys: Tuple[str, ...]
            for a2 in arities:
                for ys in permutations(myvars, a2):
                    if not connected(xs, ys):
                        continue
                    if not uses_in_order(xs, ys):
                        continue
                    pairs.add(cast(Tuple[Tuple[str, ...], Tuple[str, ...]],
                              tuple(sorted([xs, ys]))))
        return sorted(pairs)

    pairs = make_pairs()
    # with open("/tmp/pairs.txt", 'w') as fp:
    #     for xs, ys in pairs:
    #         print(f"xs = {xs}, ys = {ys}", file=fp)

    # pairs2 appears to be a subset of pairs with some redundancies
    # (based on equivalent namings), removed.
    pairs2: set[Tuple[Tuple[str, ...], Tuple[str, ...]]] = set()

    def make_pairs2() -> None:
        lookup: Dict[str, int]
        for xs, ys in pairs:
            lookup = {}

            def tmp(vs: Tuple[str, ...], next_var: int) -> Tuple[Tuple[str, ...], int]:
                out = []
                for v in vs:
                    if v not in lookup:
                        lookup[v] = next_var
                        next_var += 1
                    k = lookup[v]
                    out.append(chr(ord('A') + k))
                return tuple(out), next_var

            var_count = 0
            out_xs, var_count = tmp(xs, var_count)
            out_ys, var_count = tmp(ys, var_count)
            # out_zs, var_count = tmp(zs, var_count)
            pairs2.add((out_xs, out_ys))

    make_pairs2()

    # with open("/tmp/pairs2.txt", 'w') as fp:
    #     for xs, ys in pairs2:
    #         print(f"xs = {xs}, ys = {ys}", file=fp)
    # print(f"length of pairs2 is {len(pairs2)}")

    # swap xs and ys if ys are longer than xs
    def make_pairs3() -> set[Tuple[Tuple[str, ...], Tuple[str, ...]]]:
        lookup: Dict[str, int]
        pair3_count = 0
        pairs3 = set()
        for xs, ys in pairs2:
            lookup = {}

            def tmp(vs: Tuple[str, ...], next_var: int) -> Tuple[Tuple[str, ...], int]:
                out = []
                for v in vs:
                    if v not in lookup:
                        lookup[v] = next_var
                        next_var += 1
                    k = lookup[v]
                    out.append(chr(ord('A') + k))
                # print(f"Transforming {vs} to {tuple(out)}")
                return tuple(out), next_var

            var_count = 0
            # swap xs and ys if xs are shorter than ys.
            if len(ys) > len(xs):
                x, y = ys, xs
            else:
                x, y = xs, ys
            out_xs, var_count = tmp(x, var_count)
            out_ys, var_count = tmp(y, var_count)
            # print(f"Before adding {out_xs, out_ys}, pairs3 has {len(pairs3)} elements.")
            k = (out_xs, out_ys)
            pairs3.add(k)
            # print(f"After adding {k}, pairs3 has {len(pairs3)} elements.")
            pair3_count += 1
        # print(f"Have added {pair3_count} entries to pairs3")
        # print(f"Length of pairs3 is {len(pairs3)}")
        return pairs3

    pairs3 = make_pairs3()
    # print(f"After return, length of pairs3 is {len(pairs3)}")

    # with open("/tmp/pairs3.txt", 'w') as fp:
    #     for xs, ys in pairs3:
    #         print(f"xs = {xs}, ys = {ys}", file=fp)

    props = []
    cons = []
    for xs, ys in pairs3:
        xs_set = set(xs)
        ys_set = set(ys)

        left = ''.join(x.lower() for x in xs)
        right = ''.join(y.lower() for y in ys)

        t_left = ','.join(f'T{x}' for x in xs)
        t_right = ','.join(f'T{y}' for y in ys)

        zs = []
        for y in ys:
            if y not in xs_set:
                zs.append('_')
            else:
                zs.append(y)

        atom_left = ','.join(xs)
        atom_right = ','.join(zs)

        if len(xs) == 1:
            t_left += ','
            atom_left += ','
        if len(ys) == 1:
            t_right += ','
            atom_right += ','

        # # IMPLIES NOT
        # key = f'not_{left}_implies_{right}'
        key = f'not_{left}_{right}'



        # if the vars are identical then remove symmetries
        sym_con = ''
        if xs == ys:
            sym_con = 'P<Q,'

        l1 = f'prop({key},(P,Q)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), type(P,({t_left})), type(Q,({t_right})), holds(P,({atom_left})), not {key}_aux((P,Q)).'
        l2 = f'{key}_aux((P,Q)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), type(P,({t_left})), type(Q,({t_right})), holds(P,({atom_left})), holds(Q,({atom_right})).'
        props.extend([l1, l2])

        con1 = f':- prop({key},(P,Q)), body_literal(Rule,P,_,({atom_left})), body_literal(Rule,Q,_,({atom_right})).'
        cons.append(con1)

        if not ys_set.issubset(xs_set):
            continue

        # IMPLIES
        key = f'{left}_{right}'


        # if the vars are identical then remove symmetries
        sym_con = ''
        if xs == ys:
            sym_con = 'P!=Q,'

        l1 = f'prop({key},(P,Q)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), type(P,({t_left})), type(Q,({t_right})), holds(P,({atom_left})), holds(Q,({atom_right})), not {key}_aux((P,Q)).'
        l2 = f'{key}_aux((P,Q)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), type(P,({t_left})), type(Q,({t_right})), holds(P,({atom_left})), not holds(Q,({atom_right})).'
        props.extend([l1, l2])


        # rule_vars = xs_set | ys_set
        rule_vars = ys_set
        assert rule_vars, \
            f"Must be rule vars to generate constraint from xs = {xs} and ys = {ys}"
        checker = ','.join(f'valid_var(Rule,{v})' for v in rule_vars)
        con1 = f':- prop({key},(P,Q)), body_literal(Rule,P,_,({atom_left})), body_literal(Rule,Q,_,({atom_right})), {checker}.'
        # con1 = f':- prop({key},(P,Q)), body_literal(Rule,P,_,({atom_left})), body_literal(Rule,Q,_,({atom_right})).'
        # print(con1)
        cons.append(con1)

    return props, cons


def has_unordered_vars(xs: List[str], ys: List[str]) -> bool:
    """
    Check to see if the set of variables, `xs` union `ys` contains
    unordered variables.
    """
    lookup = {}

    def tmp(vs: Iterable[str], next_var: int) -> Tuple[Tuple[str, ...], int]:
        out = []
        for v in vs:
            if v not in lookup:
                lookup[v] = next_var
                next_var += 1
            k = lookup[v]
            out.append(chr(ord('A') + k))
        return tuple(out), next_var

    var_count = 0
    out_xs, var_count = tmp(xs, var_count)
    out_ys, var_count = tmp(ys, var_count)
    z1 = tuple(sorted([xs, ys]))
    z2 = tuple(sorted([out_xs, out_ys]))
    return z1 != z2


def rename_variables(xs: Iterable[str], ys: Iterable[str]) -> Tuple[str, str]:
    lookup: Dict[str, int] = {}

    def tmp(vs: Iterable[str], next_var: int) -> Tuple[Tuple[str, ...], int]:
        # print(type(vs), vs)
        # exit()
        out = []
        for v in vs:
            if v not in lookup:
                lookup[v] = next_var
                next_var += 1
            k = lookup[v]
            out.append(chr(ord('A') + k))
        return tuple(out), next_var
    var_count = 0
    xs, var_count = tmp(xs, var_count)
    ys, var_count = tmp(ys, var_count)
    # xs, ys = sorted([xs, ys], key=lambda x: len(x), reverse=True)
    new_xs = ''.join(x.lower() for x in xs)
    new_ys = ''.join(y.lower() for y in ys)
    return new_xs, new_ys


def build_props2(settings: Settings, arities: Iterable[int]) -> Tuple[List[str], List[str]]:
    """
    Based on `settings` and `arities`, return a list of propositions and a list of constraints.
    """
    # premise1 = []

    arities = [x for x in arities if x < 3]
    # arities = [x for x in arities if x < 2]

    myvars = all_myvars[:settings.max_vars]

    triples_list: List[Tuple[Tuple[str, ...], Tuple[str, ...], Tuple[str, ...]]] = []

    def make_triples_list() -> None:
        for a1 in arities:
            xs = tuple(myvars[:a1])
            # xs_set = set(xs)
            for a2 in arities:
                for ys in permutations(myvars, a2):
                    if not connected(xs, ys):
                        continue
                    if not uses_in_order(xs, ys):
                        continue
                    xs_ys = set(xs) | set(ys)
                    for a3 in arities:
                        for zs in permutations(myvars, a3):
                            if not connected(xs_ys, zs):
                                continue
                            if not uses_in_order(xs_ys, zs):
                                continue
                            # print(xs,ys,zs)
                            # TODO: RENAME VARIABLES
                            triples_list.append((xs, ys, zs))

    make_triples_list()

    # for x in pairs:
    #     print(x)
    triples2 = set()

    def make_triples2() -> None:
        lookup: dict[str, int]
        for xs, ys, zs in triples_list:
            lookup = {}

            def tmp(vs: Iterable[str], next_var: int) -> Tuple[Tuple[str, ...], int]:
                out = []
                for v in vs:
                    if v not in lookup:
                        lookup[v] = next_var
                        next_var += 1
                    k = lookup[v]
                    out.append(chr(ord('A') + k))
                return tuple(out), next_var
            var_count = 0
            xs, ys, zs = sorted([xs, ys, zs], key=lambda x: len(x), reverse=True)
            out_xs, var_count = tmp(xs, var_count)
            out_ys, var_count = tmp(ys, var_count)
            out_zs, var_count = tmp(zs, var_count)
            triples2.add((out_xs, out_ys, out_zs))

    make_triples2()

    Triple = Tuple[Tuple[str, ...], Tuple[str, ...], Tuple[str, ...]]
    seen_map: dict[Tuple[frozenset[Tuple[str, ...]], Tuple[str, ...]], Triple] = {}

    triples3 = set()

    def make_triples3() -> None:
        seen: set[Tuple[frozenset[Tuple[str, ...]], Tuple[str, ...]]] = set()
        for xs, ys, zs in triples2:
            k: Tuple[frozenset[Tuple[str, ...]], Tuple[str, ...]] = \
                frozenset((xs, ys)), zs
            if k in seen:
                # print('match')
                # print(xs, ys, zs)
                # print(seen_map[k])
                continue
            seen.add(k)
            seen_map[k] = (xs, ys, zs)

            # if len(xs) > len(ys):
            #     # print('1', xs, ys, zs)
            #     continue
            # else:
            # print(xs, ys, zs)
            triples3.add((xs, ys, zs))

    make_triples3()

    pairs = triples2
    props: List[str] = []
    cons: List[str] = []
    seen = set()
    for xs, ys, zs in pairs:
        xs_set = set(xs)
        ys_set = set(ys)
        zs_set = set(zs)

        a1 = ''.join(x.lower() for x in xs)
        a2 = ''.join(y.lower() for y in ys)
        a3 = ''.join(z.lower() for z in zs)

        t1 = ','.join(f'T{x}' for x in xs)
        t2 = ','.join(f'T{y}' for y in ys)
        t3 = ','.join(f'T{z}' for z in zs)

        smoother = []
        xs_ys_set = xs_set | ys_set
        for z in zs:
            if z not in xs_ys_set:
                smoother.append('_')
            else:
                smoother.append(z)

        smoothed = ','.join(smoother)
        if len(zs) == 1:
            smoothed += ','

        atom1 = ','.join(xs)
        atom2 = ','.join(ys)
        atom3 = ','.join(zs)

        if len(xs) == 1:
            t1 += ','
            atom1 += ','
        if len(ys) == 1:
            t2 += ','
            atom2 += ','
        if len(zs) == 1:
            t3 += ','
            atom3 += ','

        # # IMPLIES NOT
        key = f'not_{a1}_{a2}_{a3}'

        if frozenset([a1, a2, a3]) in seen:
            continue
        seen.add(frozenset([a1, a2, a3]))



        # # if the vars are identical then remove symmetries
        sym_con = ''
        if xs == ys:
            sym_con += 'P<Q,'
        if xs == zs:
            sym_con += 'P<R,'
        if ys == zs:
            sym_con += 'Q<R,'

        aux_key: str = f'{key}_subsumed'
        aux1 = f'{aux_key}(P,Q,R):- body_pred(P,_), body_pred(Q,_), body_pred(R,_), prop(not_{a1}_{a2},(P,Q)).'
        aux2 = f'{aux_key}(P,Q,R):- body_pred(P,_), body_pred(Q,_), body_pred(R,_), prop(not_{a1}_{a3},(P,R)).'
        aux3 = f'{aux_key}(P,Q,R):- body_pred(P,_), body_pred(Q,_), body_pred(R,_), prop(not_{a2}_{a3},(Q,R)).'
        props.extend([aux1, aux2, aux3])
        # props.extend([aux2, aux3])

        a1_, a2_ = rename_variables(a1, a2)
        aux1 = f'{aux_key}(P,Q,R):- body_pred(P,_), body_pred(Q,_), body_pred(R,_), prop(not_{a1_}_{a2_},(P,Q)).'
        a1_, a3_ = rename_variables(a1, a3)
        aux2 = f'{aux_key}(P,Q,R):- body_pred(P,_), body_pred(Q,_), body_pred(R,_), prop(not_{a1_}_{a3_},(P,R)).'
        a2_, a3_ = rename_variables(a2, a3)
        aux3 = f'{aux_key}(P,Q,R):- body_pred(P,_), body_pred(Q,_), body_pred(R,_), prop(not_{a2_}_{a3_},(Q,R)).'
        props.extend([aux1, aux2, aux3])


        l1 = f'prop({key},(P,Q,R)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), body_pred(R,{len(zs)}), type(P,({t1})), type(Q,({t2})), type(R,({t3})), holds(P,({atom1})), holds(Q,({atom2})), not {key}_aux((P,Q,R)), not {aux_key}(P,Q,R).'
        l2 = f'{key}_aux((P,Q,R)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), body_pred(R,{len(zs)}), type(P,({t1})), type(Q,({t2})), type(R,({t3})), holds(P,({atom1})), holds(Q,({atom2})), holds(R,({atom3})), not {aux_key}(P,Q,R).'

        # l1 = f'prop({key},(P,Q,R)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), body_pred(R,{len(zs)}), type(P,({t1})), type(Q,({t2})), type(R,({t3})), holds(P,({atom1})), holds(Q,({atom2})), not {key}_aux((P,Q,R)).'
        # l2 = f'{key}_aux((P,Q,R)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), body_pred(R,{len(zs)}), type(P,({t1})), type(Q,({t2})), type(R,({t3})), holds(P,({atom1})), holds(Q,({atom2})), holds(R,({atom3})).'

        props.extend([l1, l2])

        # print(l1)
        # print(l2)

        con1 = f':- prop({key},(P,Q,R)), body_literal(Rule,P,_,({atom1})), body_literal(Rule,Q,_,({atom2})), body_literal(Rule,R,_,({atom3})).'
        cons.append(con1)

        if not zs_set.issubset(xs_ys_set):
            continue

        # # IMPLIES
        key = f'{a1}_{a2}_{a3}'


        aux_key = f'{key}_subsumed'
        aux1 = f'{aux_key}(P,Q,R):- body_pred(P,_), body_pred(Q,_), body_pred(R,_), prop({a1}_{a3},(P,R)).'
        aux2 = f'{aux_key}(P,Q,R):- body_pred(P,_), body_pred(Q,_), body_pred(R,_), prop({a2}_{a3},(Q,R)).'
        props.extend([aux1, aux2])


        l1 = f'prop({key},(P,Q,R)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), body_pred(R,{len(zs)}), type(P,({t1})), type(Q,({t2})), type(R,({t3})), holds(P,({atom1})), holds(Q,({atom2})), not {key}_aux((P,Q,R)), not {aux_key}(P,Q,R).'
        l2 = f'{key}_aux((P,Q,R)):- {sym_con} body_pred(P,{len(xs)}), body_pred(Q,{len(ys)}), body_pred(R,{len(zs)}), type(P,({t1})), type(Q,({t2})), type(R,({t3})), holds(P,({atom1})), holds(Q,({atom2})), not holds(R,({smoothed})).'


        props.extend([l1, l2])


        # rule_vars = xs_set | ys_set
        rule_vars = zs_set
        checker = ','.join(f'valid_var(Rule,{v})' for v in rule_vars)
        con1 = f':- prop({key},(P,Q,R)), body_literal(Rule,P,_,({atom1})), body_literal(Rule,Q,_,({atom2})), body_literal(Rule,R,_,({atom3})), {checker}.'
        # # con1 = f':- prop({key},(P,Q)), body_literal(Rule,P,_,({atom_left})), body_literal(Rule,Q,_,({atom_right})).'
        # # print(con1)
        cons.append(con1)

    props = sorted(list(set(props)))
    return props, cons


def arg_to_symbol(arg: tuple | numbers.Number | str) -> clingo.Symbol:
    if isinstance(arg, tuple):
        return Tuple_(tuple(arg_to_symbol(a) for a in arg))
    if isinstance(arg, numbers.Number):
        if isinstance(arg, int):
            return Number(arg)
        raise TypeError(f"Got Number {arg} to translate to clingo Number, but clingo Numbers must be integers.")
    if isinstance(arg, str):
        return Function(arg)
    raise TypeError(f'Unhandled argtype({type(arg)}) in aspsolver.py arg_to_symbol()')


def atom_to_symbol(pred: str, args: Iterable[tuple | numbers.Number | str]) -> clingo.Symbol:
    xs = tuple(arg_to_symbol(arg) for arg in args)
    return Function(name = pred, arguments = xs)


def deduce_bk_cons(settings: Settings) -> List[str]:
    prog = []
    lookup2 = {k: f'({v})' for k, v in tmp_map.items()}
    lookup1 = {k: v for k, v in lookup2.items()}
    lookup1[1] = '(V0,)'
    head_pred, head_args = settings.head_literal
    head_arity = len(head_args)

    # for pred, arity in :

    arities = set()
    for p, a in settings.body_preds:
        arities.add(a)
        arg_str = lookup1[a]
        arg_str2 = lookup2[a]
        rule = f'holds({p},{arg_str}):- {p}{arg_str2}.'
        prog.append(rule)
        prog.append(f'body_pred({p},{a}).')


    # with open(settings.bias_file) as f:
    #     bias = f.read()
    #     for p,a in settings.pointless:
    #         bias = re.sub(rf'body_pred\({p},{a}\).','', bias)


    # encoding = []
    # ADD VARS, DIRECTIONS, AND TYPES
    # head_arity = len(settings.head_literal.arguments)
    # encoding.append(f'head_vars({head_arity}, {tuple(range(head_arity))}).')
    # arities = set(a for p, a in self.settings.body_preds)
    # arities.add(head_arity)
    # for arity in arities:
    #     for xs in permutations(range(settings.max_vars), arity):
    #         encoding.append(f'vars({arity}, {tuple(xs)}).')
    #         for i, x in enumerate(xs):
    #             encoding.append(f'var_pos({x}, {tuple(xs)}, {i}).')

    # type_encoding = set()
    if settings.head_types:
        type_tuple = tuple(settings.head_types)
        prog.append(f'type({settings.head_literal[0]},{type_tuple}).')

        for p, t in settings.body_types.items():
            type_tuple = tuple(t)
            prog.append(f'type({p},{type_tuple}).')
        # encoding.extend(type_encoding)

    prog_str = '\n'.join(prog)

    with open(settings.bk_file) as f:
        bk = f.read()

    bk = bk.replace('\\+', 'not')

    new_props1, new_cons1 = build_props(settings, arities)
    new_props2, new_cons2 = build_props2(settings, arities)

    new_props_list: List[str] = new_props1 + new_props2
    new_cons: List[str] = new_cons1 + new_cons2

    # print('\n'.join(new_cons))

    new_props = '\n'.join(new_props_list)
    encoding_list = [prog_str, bk, TIDY_OUTPUT, new_props]

    if settings.head_types is None:
        if head_arity == 1:
            types = '(t,)'
        else:
            # print('head_arity', head_arity)
            types = str(tuple(['t'] * head_arity))
        encoding_list.append(f'type({head_pred},{types}).')

    if len(settings.body_types) == 0:
        # exit()
        for p, a in settings.body_preds:
            if a == 1:
                types = '(t,)'
            else:
                types = str(tuple(['t'] * a))

            encoding_list.append(f'type({p},{types}).')

    encoding = '\n'.join(encoding_list)
    solver = clingo.Control(['-Wnone'])
    solver.add('base', [], encoding)
    solver.ground([('base', [])])
    out = set()

    # implies_not = []

    with solver.solve(yield_=True) as handle:
        for m in handle:
            for atom in m.symbols(shown = True):
                # args = atom.arguments
                if atom.name == 'prop':
                    out.add(str(atom))
    xs: List[str] = [x + '.' for x in out]
    return xs + new_cons


def generate_binary_strings(bit_count: int) -> List[Tuple[Bit, ...]]:
    return list(cast(Iterable[Tuple[Bit, ...]], product((0,1), repeat=bit_count)))[1:-1]


# pylint: disable=too-many-branches,too-many-statements, broad-exception-caught
def deduce_recalls(settings: Settings) -> List[str] | None:
    # Jan Struyf, Hendrik Blockeel: Query Optimization in Inductive Logic Programming by Reordering Literals. ILP 2003: 329-346

    counts: Dict[str, Dict[Tuple[Bit, ...], Dict[Tuple, set]]] = {}
    counts_all: Dict[str, int] = {}

    try:
        with open(settings.bk_file) as f:
            bk = f.read()
        solver = clingo.Control(['-Wnone'])
        with suppress_stdout_stderr():
            solver.add('base', [], bk)
            solver.ground([('base', [])])
    except Exception as Err:
        settings.logger.error(f'ERROR deducing recalls: {Err}')
        traceback.print_exc(None, file=sys.stderr)
        return None

    for pred, arity in settings.body_preds:
        counts_all[pred] = 0
        counts[pred] = {}
        d = counts[pred]
        binary_strings: List[Tuple[Bit, ...]] = generate_binary_strings(arity)
        var_subset: Tuple[Bit, ...]
        for var_subset in binary_strings:
            d[var_subset] = defaultdict(set)

        for atom in solver.symbolic_atoms.by_signature(pred, arity=arity):
            counts_all[pred] += 1

            args: List[str] = list(map(str, atom.symbol.arguments))

            for var_subset in binary_strings:
                key: List[str] = []
                value: List[str] = []
                for i in range(arity):
                    if var_subset[i]:
                        key.append(args[i])
                    else:
                        value.append(args[i])
                tkey = tuple(key)
                tvalue = tuple(value)
                d[var_subset][tkey].add(tvalue)

    # we now calculate the maximum recall
    all_recalls: Dict[Tuple[str, Tuple[int, ...]], int] = {}
    recall: int
    for pred, arity in settings.body_preds:
        d1 = counts[pred]
        all_recalls[(pred, (0,)*arity)] = counts_all[pred]
        for args2, d2 in d1.items():
            try:
                recall = max(len(xs) for xs in d2.values())
            except ValueError:
                settings.logger.error(f"Failed to recall consequences of body predicate {pred}/{arity}")
                settings.logger.error("Setting recall count to 0 and continuing")
                recall = 0
            # print(pred, args2, recall)
            all_recalls[(pred, args2)] = recall

    settings.recall = cast(dict[Tuple[str, Tuple[Bit, ...]], int], settings.recall | all_recalls)

    # for k, v in sorted(settings.recall.items()):
        # print(k ,v)

    out = []

    for (pred, val), recall in all_recalls.items():
        if recall > 4:
            continue
        if 1 not in val:
            pass
        arity = len(val)
        args = [f'V{i}' for i in range(arity)]
        args_str = ','.join(args)

        if len(args) == 1:
            args_str += ','
        subset = []
        fixer = []

        for x, y in zip(val, args):
            if x == 0:
                subset.append(y)
                fixer.append('_')
            else:
                fixer.append(y)

        subset_str = ','.join(subset)
        fixer_str = ','.join(fixer)
        if len(fixer) == 1:
            fixer_str += ','
        con2 = f':- body_literal(Rule,{pred},_,({fixer_str})), #count{{{subset_str}: body_literal(Rule,{pred},_,({args_str}))}} > {recall}.'
        out.append(con2)

    return out


def deduce_type_cons(settings: Settings) -> Iterator[str]:

    body_types = settings.body_types

    if len(body_types) == 0:
        return

    type_objects = defaultdict(set)

    with open(settings.bk_file) as f:
        bk = f.read()
    solver = clingo.Control(['-Wnone'])
    solver.add('base', [], bk)
    solver.ground([('base', [])])

    for pred, arity in settings.body_preds:
        for atom in solver.symbolic_atoms.by_signature(pred, arity=arity):
            # args = []
            for i in range(arity):
                arg = atom.symbol.arguments[i]
                x = str(arg)
                arg_type = body_types[pred][i]
                type_objects[arg_type].add(x)

    for k, vs in type_objects.items():
        n = len(vs)
        if n > settings.max_vars:
            continue
        if settings.showcons:
            print('max_vars', k, len(vs))
        con = ":- clause(C), #count{V : var_type(C, V," + k + ")} > " + str(n) + "."
        # print(con)
        yield con


SINGLETON_ENCODING = """
#show total/2.
#show total2/3.
#show total3/4.
#show total4/5.
not_total(P, I):-
    type(P, I, T),
    domain(T, X), not holds(P,I,X),
    pred(P,_).

total(P, I):-
    type(P, I, _),
    not not_total(P, I),
    pred(P,_).


not_total2(P, I, J):-
    pred(P,A),
    A>2,
    I < J,
    type(P, I, T1),
    type(P, J, T2),
    domain(T1, X),
    domain(T2, Y),
    not holds2(P, I, J, X, Y).

total2(P, I, J):-
    pred(P, A),
    A>2,
    type(P, I, _),
    type(P, J, _),
    I < J,
    not not_total2(P, I, J).


not_total3(P, I, J, K):-
    pred(P,A),
    A>3,
    I < J,
    J < K,
    type(P, I, T1),
    type(P, J, T2),
    type(P, K, T3),
    domain(T1, X),
    domain(T2, Y),
    domain(T3, Z),
    not holds3(P, I, J, K, X, Y, Z).

total3(P, I, J, K):-
    pred(P, A),
    A>3,
    type(P, I, _),
    type(P, J, _),
    type(P, K, _),
    I < J,
    J < K,
    not not_total3(P, I, J, K).

not_total4(P, I1, I2, I3, I4):-
    pred(P,A),
    A>4,
    I1 < I2,
    I2 < I3,
    I3 < I4,
    type(P, I1, T1),
    type(P, I2, T2),
    type(P, I3, T3),
    type(P, I4, T4),
    domain(T1, X1),
    domain(T2, X2),
    domain(T3, X3),
    domain(T4, X4),
    not holds4(P, I1, I2, I3, I4, X1, X2, X3, X4).

total4(P, I1, I2, I3, I4):-
    pred(P,A),
    A>4,
    I1 < I2,
    I2 < I3,
    I3 < I4,
    type(P, I1, T1),
    type(P, I2, T2),
    type(P, I3, T3),
    type(P, I4, T4),
    not not_total4(P, I1, I2, I3, I4).
"""


def deduce_non_singletons(settings: Settings) -> List[str]:
    encoding: List[str] = []

    if len(settings.body_types) == 0:
        return []

    for p, a in settings.body_preds:

        if a > 1:
            encoding.append(f'pred({p},{a}).')

        types = settings.body_types[p]
        for i, t in enumerate(types):
            rule = f'domain({t},X):- holds({p},{i},X).'
            encoding.append(rule)
            rule = f'type({p},{i},{t}).'
            encoding.append(rule)

        args = [f'V{i}' for i in range(a)]
        arg_str = ','.join(args)
        # for i in range(a):

        for i in range(a):

            rule = f'holds({p},{i},{args[i]}):- {p}({arg_str}).'
            encoding.append(rule)

            x = args[i]
            for j in range(i+1, a):
                y = args[j]
                rule = f'holds2({p},{i},{j},{x},{y}):- {p}({arg_str}).'
                encoding.append(rule)

                for k in range(j+1, a):
                    z = args[k]
                    rule = f'holds3({p},{i},{j},{k},{x},{y},{z}):- {p}({arg_str}).'
                    encoding.append(rule)

                    for i_4 in range(k+1, a):
                        x_4 = args[i_4]
                        rule = f'holds4({p},{i},{j},{k},{i_4},{x},{y},{z},{x_4}):- {p}({arg_str}).'
                        encoding.append(rule)

    encoding = sorted(encoding)
    encoding.append(SINGLETON_ENCODING)

    with open(settings.bk_file) as f:
        bk = f.read()

    encoding.append(bk)
    encoding_str = '\n'.join(encoding)

    # with open('TOTAL', 'w') as f:
        # f.write(encoding)

    solver = clingo.Control(['-Wnone'])
    solver.add('base', [], encoding_str)
    solver.ground([('base', [])])

    cons = []

    pred_lookup = {p:a for p,a in settings.body_preds}

    seen: Dict[str, set[frozenset[str]]] = defaultdict(set)
    for atom in solver.symbolic_atoms.by_signature('total4', arity=5):
        p = str(atom.symbol.arguments[0])
        i = int(atom.symbol.arguments[1].number)
        j = int(atom.symbol.arguments[2].number)
        k = int(atom.symbol.arguments[3].number)
        i_4 = int(atom.symbol.arguments[4].number)
        a = pred_lookup[p]
        args = [f'V{i}' for i in range(a)]
        arg_str = ','.join(args)
        total_x = args[i]
        total_y = args[j]
        total_z = args[k]
        x_4 = args[i_4]

        singletons_checked = frozenset([v for v in args if v not in (total_x, total_y, total_z, x_4)])

        non_singletons = ','.join(f'singleton({v})' for v in args if v not in (total_x, total_y, total_z, x_4))
        con = f':- body_literal(_, {p}, _, ({arg_str})), {non_singletons}.'

        if any(x.issubset(singletons_checked) for x in seen[p]):
            # print(atom.symbol)
            # print('skip', con)
            continue
        cons.append(con)
        # print('MOOOO', con)
        seen[p].add(singletons_checked)

    for atom in solver.symbolic_atoms.by_signature('total3', arity=4):
        p = str(atom.symbol.arguments[0])
        i = int(atom.symbol.arguments[1].number)
        j = int(atom.symbol.arguments[2].number)
        k = int(atom.symbol.arguments[3].number)
        a = pred_lookup[p]
        args = [f'V{i}' for i in range(a)]
        arg_str = ','.join(args)
        total_x = args[i]
        total_y = args[j]
        total_z = args[k]

        singletons_checked = frozenset([v for v in args if v not in (total_x, total_y, total_z)])

        non_singletons = ','.join(f'singleton({v})' for v in args if v not in (total_x, total_y, total_z))
        con = f':- body_literal(_, {p}, _, ({arg_str})), {non_singletons}.'

        if any(x.issubset(singletons_checked) for x in seen[p]):
            # print(atom.symbol)
            # print('skip', con)
            continue
        cons.append(con)
        seen[p].add(singletons_checked)

    for atom in solver.symbolic_atoms.by_signature('total2', arity=3):
        p = str(atom.symbol.arguments[0])
        i = int(atom.symbol.arguments[1].number)
        j = int(atom.symbol.arguments[2].number)
        a = pred_lookup[p]
        args = [f'V{i}' for i in range(a)]
        arg_str = ','.join(args)
        total_x = args[i]
        total_y = args[j]
        singletons_checked = frozenset([v for v in args if v not in (total_x, total_y)])
        non_singletons = ','.join(f'singleton({v})' for v in args if v not in (total_x, total_y))
        con = f':- body_literal(_, {p}, _, ({arg_str})), {non_singletons}.'

        if any(x.issubset(singletons_checked) for x in seen[p]):
            # print(atom.symbol)
            # print('skip', con)
            continue

        # print('keep', con)
        cons.append(con)
        seen[p].add(singletons_checked)

    for atom in solver.symbolic_atoms.by_signature('total', arity=2):
        p = str(atom.symbol.arguments[0])
        i = int(atom.symbol.arguments[1].number)
        a = pred_lookup[p]
        args = [f'V{i}' for i in range(a)]
        arg_str = ','.join(args)
        total_v = args[i]
        non_singletons = ','.join(f'singleton({v})' for v in args if v != total_v)
        singletons_checked = frozenset([v for v in args if v != total_v])
        con = f':- body_literal(_, {p}, _, ({arg_str})), {non_singletons}.'
        if any(x.issubset(singletons_checked) for x in seen[p]):
            # print('skip', con)
            continue

        # print('keep', con)
        cons.append(con)

    # exit()
    return cons
