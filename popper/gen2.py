import re
from itertools import permutations
from typing import Any, Set, Tuple, Optional, List, Iterator

import clingo
import clingo.script

from .abs_generate import Generator as AbstractGenerator
from .resources import resource_string
from .util import Constraint, Literal, Settings

DEFAULT_HEURISTIC = """
#heuristic size(N). [1000-N,true]
"""

NOISY_ENCODING = """
program_bounds(0..K):- max_size(K).
program_size_at_least(M):- size(N), program_bounds(M), M <= N.
"""


class Generator(AbstractGenerator):
    """
    This generator is for the `settings.single_solve` case.


    """
    settings: Settings
    model: Optional[clingo.Model]
    solver: clingo.Control
    handle: Optional[Iterator[clingo.Model]]

    def __init__(self, settings: Settings, bkcons: Optional[List]=None):
        self.savings = 0
        self.settings = settings
        self.cached_clingo_atoms = {}
        self.handle = None
        self.pruned_sizes = set()
        if bkcons is None:
            bkcons = list()

        encoding = self.build_encoding(bkcons, settings)

        with open('/tmp/ENCODING-GEN.pro', 'w') as f:
            f.write(encoding)

        solver = self.init_solver(encoding)
        self.solver = solver

        self.model = None

    def init_solver(self, encoding) -> clingo.Control:
        solver = clingo.Control(['--heuristic=Domain', '-Wnone'])
        solver.configuration.solve.models = 0
        solver.add('base', [], encoding)
        solver.ground([('base', [])])
        return solver

    def build_encoding(self, bkcons, settings):
        encoding = []
        alan = resource_string(__name__, "lp/alan.pl").decode()
        encoding.append(alan)
        with open(settings.bias_file) as f:
            bias_text = f.read()
        bias_text = re.sub(r'max_vars\(\d*\).', '', bias_text)
        bias_text = re.sub(r'max_body\(\d*\).', '', bias_text)
        bias_text = re.sub(r'max_clauses\(\d*\).', '', bias_text)
        # AC: NEED TO COMPLETELY REFACTOR THIS CODE
        for p, a in settings.pointless:
            bias_text = re.sub(rf'body_pred\({p},\s*{a}\)\.', '', bias_text)
            bias_text = re.sub(rf'constant\({p},.*?\).*', '', bias_text, flags=re.MULTILINE)
        encoding.append(bias_text)
        encoding.append(f'max_clauses({settings.max_rules}).')
        encoding.append(f'max_body({settings.max_body}).')
        encoding.append(f'max_vars({settings.max_vars}).')
        # ADD VARS, DIRECTIONS, AND TYPES
        head_arity = len(settings.head_literal.arguments)
        encoding.append(f'head_vars({head_arity}, {tuple(range(head_arity))}).')
        arities = set(a for p, a in self.settings.body_preds)
        arities.add(head_arity)
        for arity in arities:
            for xs in permutations(range(settings.max_vars), arity):
                encoding.append(f'vars({arity}, {tuple(xs)}).')
                for i, x in enumerate(xs):
                    encoding.append(f'var_pos({x}, {tuple(xs)}, {i}).')
                encoding.append(f'ordered_vars({tuple(xs)},{tuple(sorted(xs))}).')

        # ORDERING THINGY
        # %% appears((0,0,V0)):- body_literal(_, _, _, (V0,)), not head_var(_,V0).
        # appears((0,V0,V1)):- body_literal(_, _, _, (A,B)), ordered_vars((A,B), (V0,V1)).
        # appears((V0,V1,V2)):- body_literal(_, _, _, (A,B,C)), ordered_vars((A,B,C), (V0,V1,V2)).
        order_cons = []
        max_arity = max(arities)
        for arity in range(2, max_arity+1):
            xs1 = ','.join(f'V{i}' for i in range(arity)) # Vs
            xs2 = ','.join(f'X{i}' for i in range(arity)) # Xs

            if arity < max_arity:
                prefix = ','.join(str(0) for i in range(arity, max_arity)) + ',' + xs1
            else:
                prefix = xs1


            order_cons.append(f'appears(({prefix})):- body_literal(_,_,_,({xs2})), ordered_vars(({xs2}), ({xs1})).')

            order_cons.append(f'var_tuple(({prefix})):- body_pred(P,{arity}), vars({arity},Vars), not bad_body(P,Vars), not type_mismatch(P,Vars), ordered_vars(Vars,OrderedVars), OrderedVars=({xs1}).')


            if arity == 1:
                order_cons.append(f'var_member(V,(0,0,0,V)):-var(V).')
            else:
                order_cons.append(f'var_member(V,({prefix})):-vars(_, Vars), Vars=({xs1}), var_member(V,Vars).')
            # print(f)
            # var_member(V,(0,0,V0,V1)):-vars(_, Vars), Vars=(V0,V1), var_member(V,Vars).
            # var_member(V,(0,V0,V1,V2)):-vars(_, Vars), Vars=(V0,V1,V2), var_member(V,Vars).

        xs1 = ','.join(f'V{i}' for i in range(max_arity)) # Vs
        for k in range(max_arity):
            xs2 = ','.join(f'V{i}' for i in range(k)) # Vs
            if k > 0 and k < max_arity:
                xs2 += ','
            xs2 += ','.join(f'X{i}' for i in range(k, max_arity))
            order_cons.append(f'lower(({xs1}),({xs2})):- var_tuple(({xs1})), var_tuple(({xs2})), X{k} < V{k}.')

        for k in range(max_arity-1):
            # A,B,C,D
            v0 = f'V{k}'
            v1 = f'V{k+1}'
            order_cons.append(f'seen_lower(Vars1, V):- V={v1}-1, Vars1 = ({xs1}), {v0} < V < {v1}, lower(Vars1, Vars2), var_tuple(Vars1), appears(Vars2), var_member(V, Vars2), not head_var(_,V).')
            order_cons.append(f'gap_(({xs1}),{v1}-1):- var_tuple(({xs1})), {v0} < V < {v1}, var(V).')


        order_cons.append(f'gap(({xs1}),V):- gap_(({xs1}), _), #max' + '{X :gap_((' + xs1 + '), X)} == V.')

        order_cons.append(f':- appears(({xs1})), gap(({xs1}), V), not seen_lower(({xs1}),V), not head_var(_,V).')

        # print('\n'.join(order_cons))
        encoding.extend(order_cons)

        type_encoding = set()
        if self.settings.head_types:
            types = tuple(self.settings.head_types)
            str_types = str(types).replace("'", "")
            for i, x in enumerate(self.settings.head_types):
                type_encoding.add(f'type_pos({str_types}, {i}, {x}).')

            for pred, types in self.settings.body_types.items():
                types = tuple(types)
                str_types = str(types).replace("'", "")
                for i, x in enumerate(types):
                    type_encoding.add(f'type_pos({str_types}, {i}, {x}).')
            encoding.extend(type_encoding)
        for pred, xs in self.settings.directions.items():
            for i, v in xs.items():
                if v == '+':
                    encoding.append(f'direction_({pred}, {i}, in).')
                if v == '-':
                    encoding.append(f'direction_({pred}, {i}, out).')
        max_size = (1 + settings.max_body) * settings.max_rules
        if settings.max_literals < max_size:
            encoding.append(f'custom_max_size({settings.max_literals}).')
        if settings.noisy:
            encoding.append(NOISY_ENCODING)
        encoding.extend(bkcons)
        if settings.single_solve:
            encoding.append(DEFAULT_HEURISTIC)
        encoding = '\n'.join(encoding)
        return encoding

    def update_solver(self, size):
        # not used when learning programs without pi or recursion
        pass

    def get_prog(self):
        if self.handle is None:
            self.handle = iter(self.solver.solve(yield_=True))
        self.model = next(self.handle, None)
        if self.model is None:
            return None

        return self.parse_model_single_rule(self.model.symbols(shown=True))



    def prune_size(self, size):
        if size in self.pruned_sizes:
            return
        self.pruned_sizes.add(size)
        size_con = [(AbstractGenerator.atom_to_symbol("size", (size,)), True)]
        self.model.context.add_nogood(size_con)

    def constrain(self, tmp_new_cons):
        new_ground_cons = set()

        for xs in tmp_new_cons:
            con_type = xs[0]
            con_prog = xs[1]

            if con_type == Constraint.GENERALISATION or con_type == Constraint.BANISH:
                con_size = None
                if self.settings.noisy and len(xs) > 2:
                    con_size = xs[2]
                # print('gen', con_type)
                ground_rules2 = tuple(self.build_generalisation_constraint3(con_prog, con_size))
                new_ground_cons.update(ground_rules2)
            elif con_type == Constraint.SPECIALISATION:
                con_size = None
                if self.settings.noisy and len(xs) > 2:
                    con_size = xs[2]
                ground_rules2 = tuple(self.build_specialisation_constraint3(con_prog, con_size))
                new_ground_cons.update(ground_rules2)
            elif con_type == Constraint.UNSAT:
                cons_ = self.unsat_constraint2(con_prog)
                new_ground_cons.update(cons_)

        self.instantiate_constraints(new_ground_cons)


    def unsat_constraint2(self, body):
        # if no types, remap variables
        if len(self.settings.body_types) == 0:
            _, body = remap_variables((None, body))

        assignments = self.find_deep_bindings4(body)
        for assignment in assignments:
            rule = []
            for pred, args in body:
                args2 = tuple(assignment[x] for x in args)
                rule.append((True, 'body_literal', (0, pred, len(args), args2)))

            yield frozenset(rule)

    def build_generalisation_constraint3(self, prog, size=None):
        rule = tuple(prog)[0]
        for body in self.find_variants(rule, max_rule_vars=True):
            body = list(body)
            body.append((True, 'body_size', (0, len(body))))
            if size:
                body.append((True, 'program_size_at_least', (size,)))
            yield frozenset(body)

    def build_specialisation_constraint3(self, prog, size=None):
        rule = tuple(prog)[0]
        if not size:
            yield from self.find_variants(rule)
            return

        for body in self.find_variants(rule):
            body = list(body)
            body.append((True, 'program_size_at_least', (size,)))
            yield frozenset(body)

    def find_variants(self, rule, max_rule_vars=False):
        head, body = rule
        body_vars = frozenset(x for literal in body for x in literal.arguments if x >= len(head.arguments))
        if max_rule_vars:
            subset = range(len(head.arguments), len(body_vars | set(head.arguments)))
        else:
            subset = range(len(head.arguments), self.settings.max_vars)
        for xs in permutations(subset, len(body_vars)):
            xs = head.arguments + xs
            new_body = []
            for pred, args in body:
                new_args = tuple(xs[arg] for arg in args)
                new_literal = (True, 'body_literal', (0, pred, len(new_args), new_args))
                new_body.append(new_literal)
            yield frozenset(new_body)

    def find_deep_bindings4(self, body):
        head_types = self.settings.head_types
        body_types = self.settings.body_types

        # if no types, find all permutations of variables
        if len(body_types) == 0 or head_types is None:
            num_vars = len({var for atom in body for var in atom.arguments})
            for xs in permutations(range(self.settings.max_vars), num_vars):
                x = {i: xs[i] for i in range(num_vars)}
                yield x
            return

        # if there are types, only find type-safe permutations
        var_type_lookup = {i: head_type for i, head_type in enumerate(head_types)}

        head_vars = set(range(len(self.settings.head_literal.arguments)))
        body_vars = set()

        for pred, args in body:
            for i, x in enumerate(args):
                body_vars.add(x)
                if x in head_vars:
                    continue
                if pred in body_types:
                    var_type_lookup[x] = body_types[pred][i]

        # prohibit bad type matchings
        bad_type_matching = set()
        for x in body_vars:
            if x not in var_type_lookup:
                continue
            for y in head_vars:
                if y not in var_type_lookup:
                    continue
                if var_type_lookup[x] == var_type_lookup[y]:
                    continue
                k = (x, y)
                bad_type_matching.add(k)

        lookup = {x: i for i, x in enumerate(body_vars)}

        for xs in permutations(range(self.settings.max_vars), len(lookup)):
            assignment = {}
            bad = False
            for x in body_vars:
                v = xs[lookup[x]]
                if (x, v) in bad_type_matching:
                    bad = True
                    break
                assignment[x] = v
            if bad:
                continue
            yield assignment


def remap_variables(rule: Tuple[Optional[Literal],Any]):
    head: Optional[Literal]
    head, body = rule
    head_vars: Set = set()

    if head:
        head_vars |= head.arguments

    next_var = len(head_vars)
    lookup = {i: i for i in head_vars}

    new_body = set()
    for pred, args in body:
        new_args = []
        for var in args:
            if var not in lookup:
                lookup[var] = next_var
                next_var += 1
            new_args.append(lookup[var])
        new_atom = Literal(pred, tuple(new_args))
        new_body.add(new_atom)

    return head, frozenset(new_body)
