"""
A module for all predicate dependencies in the AST
"""
from itertools import product

import networkx as nx
from clingo.ast import ASTType, Sign


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


class PositivePredicateDependency:
    def __init__(self, prg):
        self.sccs = []
        g = nx.DiGraph()
        for stm in prg:
            if stm.ast_type == ASTType.Rule:
                heads = head_predicates(stm, {Sign.NoSign})
                bodies = body_predicates(stm, {Sign.NoSign})
                g.add_edges_from(product(map(lambda triple : (triple[1], triple[2]), bodies), map(lambda triple : (triple[1], triple[2]),heads)))
                self.sccs = list(nx.strongly_connected_components(g))

    # returns true if all of the predicates in predlist have a positive dependency with each other
    def are_dependent(self, predlist):
        spl = set(predlist)
        for scc in self.sccs:
            if spl <= scc:
                return True
        return False
