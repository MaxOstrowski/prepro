"""
A module for all predicate dependencies in the AST
"""
from collections import defaultdict
from copy import deepcopy
from itertools import chain, product

import networkx as nx
from clingo import ast
from clingo.ast import (
    AggregateFunction,
    ASTType,
    BodyAggregate,
    BodyAggregateElement,
    Comparison,
    ComparisonOperator,
    ConditionalLiteral,
    Function,
    Guard,
    Literal,
    Sign,
    SymbolicAtom,
    Variable,
)

from utils import collect_ast, contains_variable, transform_ast


def body_predicates(rule, signs):
    """
    yields all predicates used in the rule body as (name, arity) that have a sign in the set signs
    """
    if rule.ast_type == ASTType.Rule:
        for blit in rule.body:
            if blit.ast_type == ASTType.Literal:
                yield from literal_predicate(blit, signs)
                yield from headorbody_aggregate_predicate(blit.atom, signs)
                yield from aggregate_predicate(blit.atom, signs)


def literal_predicate(lit, signs):
    """converts ast Literal into (sign, name, arity) if sign is in signs"""
    if lit.ast_type == ASTType.Literal:
        if lit.sign in signs and lit.atom.ast_type == ASTType.SymbolicAtom:
            atom = lit.atom
            if atom.symbol.ast_type == ASTType.Function:
                yield (lit.sign, atom.symbol.name, len(atom.symbol.arguments))


def conditional_literal_predicate(condlit, signs):
    if condlit.ast_type != ASTType.ConditionalLiteral:
        return
    lit = condlit.literal
    yield from literal_predicate(lit, signs)
    for cond in condlit.condition:
        yield from literal_predicate(cond, signs)


def headorbody_aggregate_predicate(agg, signs):
    if agg.ast_type == ASTType.BodyAggregate or agg.ast_type == ASTType.HeadAggregate:
        for elem in agg.elements:
            if elem.ast_type == ASTType.HeadAggregateElement:
                yield from conditional_literal_predicate(elem.condition, signs)
            elif elem.ast_type == ASTType.BodyAggregateElement:
                for cond in elem.condition:
                    # aggregate in body seems to have Literals as condition
                    yield from literal_predicate(cond, signs)


def aggregate_predicate(agg, signs):
    if agg.ast_type == ASTType.Aggregate:
        for elem in agg.elements:
            yield from conditional_literal_predicate(elem, signs)
            for cond in elem.condition:
                # aggregate in body seems to have Literals as condition
                yield from literal_predicate(cond, signs)


def disjunction_predicate(head, signs):
    if head.ast_type == ASTType.Disjunction:
        for lit in head.elements:
            yield from conditional_literal_predicate(lit, signs)


def head_predicates(rule, signs):
    """
    yields all predicates used in the rule head as (name, arity) that have a sign in the set signs
    """
    if rule.ast_type == ASTType.Rule:
        head = rule.head
        yield from literal_predicate(head, signs)
        yield from aggregate_predicate(head, signs)
        yield from headorbody_aggregate_predicate(head, signs)
        yield from disjunction_predicate(head, signs)


def predicates(ast, signs):
    """
    yields all predicates in ast that have a sign in the set signs
    """
    yield from head_predicates(ast, signs)
    yield from literal_predicate(ast, signs)
    yield from aggregate_predicate(ast, signs)
    yield from headorbody_aggregate_predicate(ast, signs)
    yield from disjunction_predicate(ast, signs)
    yield from conditional_literal_predicate(ast, signs)
    yield from body_predicates(ast, signs)


def collect_bound_variables(stmlist):
    """return a list of all ast of type Variable that are in a positive symbolic literal or in a eq relation"""
    bound_variables = set()
    for stm in stmlist:
        if stm.ast_type == ASTType.Literal:
            if stm.sign == Sign.NoSign and stm.atom.ast_type == ASTType.SymbolicAtom:
                bound_variables.update(collect_ast(stm, "Variable"))
            elif stm.sign == Sign.NoSign and stm.atom.ast_type == ASTType.BodyAggregate:
                if stm.atom.left_guard.comparison == ComparisonOperator.Equal:
                    bound_variables.update(collect_ast(stm.atom.left_guard, "Variable"))
    changed = True
    while changed:
        changed = False
        for stm in stmlist:
            if stm.sign == Sign.NoSign and stm.atom.ast_type == ASTType.Comparison:
                guards = stm.atom.guards
                if any(map(lambda x: x.comparison == ComparisonOperator.Equal, guards)):
                    variables = set(collect_ast(stm, "Variable"))
                    if len(variables - bound_variables) <= 1:
                        bound_variables.update(variables)
    return bound_variables


# TODO: create predicates as NamedTuple
class PositivePredicateDependency:
    def __init__(self, prg):
        self.sccs = []
        g = nx.DiGraph()
        for stm in prg:
            if stm.ast_type == ASTType.Rule:
                heads = head_predicates(stm, {Sign.NoSign})
                bodies = body_predicates(stm, {Sign.NoSign})
                g.add_edges_from(
                    product(
                        map(lambda triple: (triple[1], triple[2]), bodies),
                        map(lambda triple: (triple[1], triple[2]), heads),
                    )
                )
        self.sccs = list(nx.strongly_connected_components(g))

    # returns true if all of the predicates in predlist have a positive dependency with each other
    def are_dependent(self, predlist):
        spl = set(predlist)
        for scc in self.sccs:
            if spl <= scc:
                return True
        return False


class DomainPredicates:
    def __init__(self, prg):
        self._no_domain = (
            set()
        )  # set of predicates that is not already a domain predicate

        prg = list(prg)
        self.domains = {}  # key = ("p",3) -> ("dom",3)
        self.domain_rules = defaultdict(list)  # atom -> [conditions, ...]
        self._too_complex = (
            set()
        )  # set of predicates that is too complex to provide a domain computation
        self.__compute_domain_predicates(prg)
        self.__compute_domains(prg)

    def __compute_domain_predicates(self, prg):
        g = nx.DiGraph()
        SIGNS = {Sign.NoSign, Sign.Negation, Sign.DoubleNegation}
        for stm in chain.from_iterable([x.unpool(condition=True) for x in prg]):
            if stm.ast_type == ASTType.Rule:
                g.add_edges_from(
                    product(
                        map(
                            lambda triple: (triple[1], triple[2]),
                            body_predicates(stm, SIGNS),
                        ),
                        map(
                            lambda triple: (triple[1], triple[2]),
                            head_predicates(stm, SIGNS),
                        ),
                    )
                )

                ### remove head choice predicates
                head = stm.head
                if head.ast_type == ASTType.Disjunction:
                    for cond in head.elements:
                        assert cond.ast_type == ASTType.ConditionalLiteral
                        lit = list(literal_predicate(cond.literal, SIGNS))[0]
                        self._no_domain.add((lit[1], lit[2]))
                elif head.ast_type == ASTType.HeadAggregate:
                    for elem in head.elements:
                        if elem.ast_type == ASTType.HeadAggregateElement:
                            cond = elem.condition
                            assert cond.ast_type == ASTType.ConditionalLiteral
                            lit = list(literal_predicate(cond.literal, SIGNS))[0]
                            self._no_domain.add((lit[1], lit[2]))
                elif head.ast_type == ASTType.Aggregate:
                    for cond in head.elements:
                        assert cond.ast_type == ASTType.ConditionalLiteral
                        lit = list(literal_predicate(cond.literal, SIGNS))[0]
                        self._no_domain.add((lit[1], lit[2]))
        cycle_free_pdg = g.copy()
        ### remove predicates in cycles
        for scc in nx.strongly_connected_components(g):
            if len(scc) > 1:
                self._no_domain.update(scc)
                cycle_free_pdg.remove_nodes_from(scc)
                self._too_complex.update(scc)
        for scc in nx.selfloop_edges(g):
            self._no_domain.add(scc[0])
            cycle_free_pdg.remove_nodes_from([scc[0]])
            self._too_complex.update([scc[0]])

        ### remove predicates derived by using non_domain predicates
        for node in nx.topological_sort(cycle_free_pdg):
            for pre in g.predecessors(node):
                if pre in self._no_domain:
                    self._no_domain.add(node)
                    continue

    def is_static(self, pred):
        """pred = (name, arity)
        returns true if predicate can be computed statically
        """
        return pred not in self._no_domain

    def has_domain(self, pred):
        """pred = (name, arity)
        returns true if a domain of pred has been computed
        """
        return self.is_static(pred) or pred in self.domains

    def domain_predicate(self, pred):
        """pred = (name, arity)
        returns domain predicate of pred
        """
        assert self.has_domain(pred)
        if self.is_static(pred):
            return pred
        return self.domains[pred]

    def min_predicate(self, pred, position):
        """pred = (name, arity)
        returns min_domain predicate of pred
        """
        return (f"__min_{position}" + self.domain_predicate(pred)[0], 1)

    def max_predicate(self, pred, position):
        """pred = (name, arity)
        returns max_domain predicate of pred
        """
        return (f"__max_{position}" + self.domain_predicate(pred)[0], 1)

    def next_predicate(self, pred, position):
        """pred = (name, arity)
        returns next_domain predicate of pred
        """
        return (f"__next_{position}" + self.domain_predicate(pred)[0], 2)

    def _domain_condition_as_string(self, pred):
        """
        function only for unit testing
        """
        if self.is_static(pred):
            return {frozenset([pred])}
        ret = set()
        for atom in self.domain_rules.keys():
            if atom.symbol.name == pred[0] and len(atom.symbol.arguments) == pred[1]:
                for conditions in self.domain_rules[atom]:
                    ret.add(frozenset([str(x) for x in conditions]))
        return ret

    def create_domain(self, pred):
        """
        given a predicate, yield a list of ast
        that represent rules to create self.domain(pred) in the logic program
        """
        if not self.has_domain(pred):
            raise RuntimeError(f"Can not create domain for {pred}.")
        if self.is_static(pred):
            return
        pos = ast.Position("<string>", 1, 1)
        loc = ast.Location(pos, pos)

        for atom in self.domain_rules.keys():
            if atom.symbol.name == pred[0] and len(atom.symbol.arguments) == pred[1]:
                for conditions in self.domain_rules[atom]:
                    newatom = ast.SymbolicAtom(
                        ast.Function(
                            loc,
                            self.domain_predicate(pred)[0],
                            atom.symbol.arguments,
                            False,
                        )
                    )
                    yield ast.Rule(loc, newatom, conditions)

    def _create_nextpred_for_domain(self, pred, position):
        """
        given a predicate, yield a list of ast
        that represent rules to create a next predicate for self.domain(pred) in the logic program
        includes min/max predicates
        The next predicate is created for the 'position's variable in the predicate, starting with 0
        """
        if not self.has_domain(pred):
            raise RuntimeError(
                f"Can not create order encoding for {pred}. Unable to create domain."
            )
        if position >= pred[1]:
            raise RuntimeError(
                f"Can not create order encoding for position {position} for {pred}. Position exceeds arity, starting with 0."
            )

        def _create_projected_lit(pred, variables, sign=Sign.NoSign):
            """
            Given a predicate pred, create a literal with only projected variables at certain positions.
            Given p/3, {1 : Variable(loc, "X"), 2: Variable(loc, "Y")} create Literal p(_,X,Y)
            """
            pos = ast.Position("<string>", 1, 1)
            loc = ast.Location(pos, pos)
            vars = [
                variables[i] if i in variables else Variable(loc, "_")
                for i in range(0, pred[1])
            ]
            return Literal(
                loc,
                sign,
                SymbolicAtom(
                    Function(
                        loc,
                        pred[0],
                        vars,
                        False,
                    )
                ),
            )

        min_pred = self.min_predicate(pred, position)
        max_pred = self.max_predicate(pred, position)
        next_pred = self.next_predicate(pred, position)
        dom_pred = self.domain_predicate(pred)

        pos = ast.Position("<string>", 1, 1)
        loc = ast.Location(pos, pos)

        var_X = Variable(loc, "X")
        var_L = Variable(loc, "L")
        var_P = Variable(loc, "P")
        var_N = Variable(loc, "N")
        var_B = Variable(loc, "B")
        dom_lit_L = _create_projected_lit(dom_pred, {position: var_X})

        min_body = Literal(
            loc,
            Sign.NoSign,
            BodyAggregate(
                loc,
                Guard(ComparisonOperator.Equal, var_X),
                AggregateFunction.Min,
                [BodyAggregateElement([var_L], [dom_lit_L])],
                None,
            ),
        )
        ### __min_0__dom_c(X) :- X = #min { L: __dom_c(X) }.
        yield ast.Rule(
            loc,
            _create_projected_lit(min_pred, {0: var_X}),
            [min_body],
        )
        max_body = Literal(
            loc,
            Sign.NoSign,
            BodyAggregate(
                loc,
                Guard(ComparisonOperator.Equal, var_X),
                AggregateFunction.Max,
                [BodyAggregateElement([var_L], [dom_lit_L])],
                None,
            ),
        )
        ### __max_0__dom_c(X) :- X = #max { L: __dom_c(X) }.
        yield ast.Rule(
            loc,
            _create_projected_lit(max_pred, {0: var_X}),
            [max_body],
        )

        ### __next_0__dom_c(P,N) :- __min_0__dom_c(P); __dom_c(N); N > P; not __dom_c(N): __dom_c(N), P < N < N.
        yield ast.Rule(
            loc,
            _create_projected_lit(next_pred, {0: var_P, 1: var_N}),
            [
                _create_projected_lit(min_pred, {0: var_P}),
                _create_projected_lit(dom_pred, {position: var_N}),
                Literal(
                    loc,
                    Sign.NoSign,
                    Comparison(var_N, [Guard(ComparisonOperator.GreaterThan, var_P)]),
                ),
                ConditionalLiteral(
                    loc,
                    _create_projected_lit(dom_pred, {position: var_B}, Sign.Negation),
                    [
                        _create_projected_lit(dom_pred, {position: var_B}),
                        Comparison(
                            var_P,
                            [
                                Guard(ComparisonOperator.LessThan, var_B),
                                Guard(ComparisonOperator.LessThan, var_N),
                            ],
                        ),
                    ],
                ),
            ],
        )

        ### __next_0__dom_c(P,N) :- __next_0__dom_c(_,P); __dom_c(N); N > P; not __dom_c(N): __dom_c(N), P < N < N.
        yield ast.Rule(
            loc,
            _create_projected_lit(next_pred, {0: var_P, 1: var_N}),
            [
                _create_projected_lit(next_pred, {1: var_P}),
                _create_projected_lit(dom_pred, {position: var_N}),
                Literal(
                    loc,
                    Sign.NoSign,
                    Comparison(var_N, [Guard(ComparisonOperator.GreaterThan, var_P)]),
                ),
                ConditionalLiteral(
                    loc,
                    _create_projected_lit(dom_pred, {position: var_B}, Sign.Negation),
                    [
                        _create_projected_lit(dom_pred, {position: var_B}),
                        Comparison(
                            var_P,
                            [
                                Guard(ComparisonOperator.LessThan, var_B),
                                Guard(ComparisonOperator.LessThan, var_N),
                            ],
                        ),
                    ],
                ),
            ],
        )

    def add_domain_rule(self, atom, bodies):
        """
        add atom <- body[0] or body[1] ... body[n] to self.domain_rules
        if it passes all checks to compute an actual domain
        inserts elements in the body as their domains
        also mark the head as not static
        """
        if atom.ast_type == ASTType.SymbolicAtom:
            self._no_domain.update([(atom.symbol.name, len(atom.symbol.arguments))])
        domain_rules = defaultdict(
            list
        )  # TODO: refactor, no intermediate map needed anymore
        domain_rules[atom] = bodies

        ### remove too complex predicates from the head
        def not_too_complex(pair):
            (head, _) = pair
            if head.ast_type == ASTType.SymbolicAtom:
                name = head.symbol.name
                arity = len(head.symbol.arguments)
                return not (name, arity) in self._too_complex
            return True

        domain_rules = dict(filter(not_too_complex, domain_rules.items()))

        # ### filter out conditions that can not be translated to domain conditions
        # ### like a sum calculation

        def is_dynamic_sum(cond):
            cond = cond.atom
            if (
                cond.ast_type == ASTType.BodyAggregate
                or cond.ast_type == ASTType.Aggregate
            ):
                for elem in cond.elements:
                    for atom in collect_ast(elem, "SymbolicAtom"):
                        name = atom.symbol.name
                        arity = len(atom.symbol.arguments)
                        if not self.is_static((name, arity)):
                            return True
            return False

        def is_too_complex(cond):
            for atom in collect_ast(cond, "SymbolicAtom"):
                name = atom.symbol.name
                arity = len(atom.symbol.arguments)
                if (name, arity) in self._too_complex:
                    return True
            return False

        def combine_filters(cond):
            return not (is_dynamic_sum(cond) or is_too_complex(cond))

        for head in domain_rules.keys():
            new_rules = []
            for conditions in domain_rules[head]:
                new_rules.append(list(filter(combine_filters, conditions)))
            domain_rules[head] = new_rules

        def has_head_bounded(pair):
            (head, bodies) = pair
            head_variables = set(map(lambda x: x.name, collect_ast(head, "Variable")))
            for conditions in domain_rules[head]:
                head_variables -= set(
                    map(lambda x: x.name, collect_bound_variables(conditions))
                )
            return len(head_variables) == 0

        domain_rules = dict(filter(has_head_bounded, domain_rules.items()))

        def have_domain(lit):
            for atom in collect_ast(lit, "SymbolicAtom"):
                if atom.symbol.ast_type == ASTType.Function:
                    if not self.has_domain(
                        (atom.symbol.name, len(atom.symbol.arguments))
                    ):
                        return False
            return True

        def replace_domain(atom):
            assert atom.ast_type == ASTType.SymbolicAtom
            assert (
                atom.symbol.ast_type == ASTType.Function
            )  # not necessary, but I still have to handle the case, TODO
            name = atom.symbol.name
            arity = len(atom.symbol.arguments)
            assert self.has_domain((name, arity))
            atom.symbol.name = self.domain_predicate((name, arity))[0]
            return atom

        for head in domain_rules.keys():
            all_domain = True
            for conditions in domain_rules[head]:
                if not all(map(have_domain, conditions)):
                    all_domain = False
            if all_domain:
                # replace all predicates with their respective domain predicates
                new_conditions = []
                for conditions in domain_rules[head]:
                    copy_conditions = deepcopy(conditions)
                    for cond in copy_conditions:
                        transform_ast(cond, "SymbolicAtom", replace_domain)
                    new_conditions.append(copy_conditions)
                domain_rules[head] = new_conditions
                self.domains[(head.symbol.name, len(head.symbol.arguments))] = (
                    "__dom_" + head.symbol.name,
                    len(head.symbol.arguments),
                )
        self.domain_rules.update(domain_rules)

    def __compute_domains(self, prg):
        """compute self.domain_rules with atom as key and a list of conditions"""
        domain_rules = defaultdict(list)
        ### collect conditions for the head
        for rule in chain.from_iterable([x.unpool(condition=True) for x in prg]):
            if rule.ast_type == ASTType.Rule:
                head = rule.head
                body = rule.body
                if (
                    head.ast_type == ASTType.Literal
                    and head.sign == Sign.NoSign
                    and head.atom.ast_type == ASTType.SymbolicAtom
                ):
                    domain_rules[head.atom].append(body)
                elif head.ast_type == ASTType.Disjunction:
                    for elem in head.elements:
                        assert elem.ast_type == ASTType.ConditionalLiteral
                        condition = elem.condition
                        if elem.literal.sign == Sign.NoSign:
                            domain_rules[elem.literal.atom].append(
                                list(chain(condition, body))
                            )
                elif head.ast_type == ASTType.HeadAggregate:
                    for elem in head.elements:
                        assert elem.condition.literal.sign == Sign.NoSign
                        domain_rules[elem.condition.literal.atom].append(
                            list(chain(elem.condition, body))
                        )
                elif head.ast_type == ASTType.Aggregate:
                    for elem in head.elements:
                        assert elem.literal.sign == Sign.NoSign
                        domain_rules[elem.literal.atom].append(
                            list(chain(elem.condition, body))
                        )
        for atom, bodies in domain_rules.items():
            pred = (atom.symbol.name, len(atom.symbol.arguments))
            if not self.is_static(pred):
                self.add_domain_rule(atom, bodies)
