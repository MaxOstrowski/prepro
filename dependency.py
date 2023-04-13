"""
A module for all predicate dependencies in the AST
"""
from itertools import product

import networkx as nx
from clingo.ast import ASTType, Sign


def positive_body_predicates(rule):
    """
    yields all predicates used in the rule body as (name, arity)
    """
    if rule.ast_type == ASTType.Rule:
        for blit in rule.body:
            if blit.ast_type == ASTType.Literal:
                yield from positive_literal_predicate(blit)
                yield from positive_headorbody_aggregate_predicate(blit.atom)
                yield from positive_aggregate_predicate(blit.atom)


def positive_literal_predicate(lit):
    if lit.ast_type == ASTType.Literal:
        if lit.sign == Sign.NoSign and lit.atom.ast_type == ASTType.SymbolicAtom:
            atom = lit.atom
            if atom.symbol.ast_type == ASTType.Function:
                yield (atom.symbol.name, len(atom.symbol.arguments))


def positive_conditional_literal_predicate(condlit):
    if condlit.ast_type != ASTType.ConditionalLiteral:
        return
    lit = condlit.literal
    yield from positive_literal_predicate(lit)
    for cond in condlit.condition:
        yield from positive_literal_predicate(cond)


def positive_headorbody_aggregate_predicate(agg):
    if agg.ast_type == ASTType.BodyAggregate or agg.ast_type == ASTType.HeadAggregate:
        for elem in agg.elements:
            if elem.ast_type == ASTType.HeadAggregateElement:
                yield from positive_conditional_literal_predicate(elem.condition)
            elif elem.ast_type == ASTType.BodyAggregateElement:
                for cond in elem.condition:
                    # aggregate in body seems to have Literals as condition
                    yield from positive_literal_predicate(cond)


def positive_aggregate_predicate(agg):
    if agg.ast_type == ASTType.Aggregate:
        for elem in agg.elements:
            yield from positive_conditional_literal_predicate(elem)
            for cond in elem.condition:
                # aggregate in body seems to have Literals as condition
                yield from positive_literal_predicate(cond)


def positive_disjunction_predicate(head):
    if head.ast_type == ASTType.Disjunction:
        for lit in head.elements:
            yield from positive_conditional_literal_predicate(lit)


def positive_head_predicates(rule):
    """
    yields all predicates used in the rule head as (name, arity)
    """
    if rule.ast_type == ASTType.Rule:
        head = rule.head
        yield from positive_literal_predicate(head)
        yield from positive_aggregate_predicate(head)
        yield from positive_headorbody_aggregate_predicate(head)
        yield from positive_disjunction_predicate(head)


def positive_predicates(ast):
    yield from positive_head_predicates(ast)
    yield from positive_literal_predicate(ast)
    yield from positive_aggregate_predicate(ast)
    yield from positive_headorbody_aggregate_predicate(ast)
    yield from positive_disjunction_predicate(ast)
    yield from positive_conditional_literal_predicate(ast)
    yield from positive_body_predicates(ast)


class PositivePredicateDependency:
    def __init__(self, prg):
        self.sccs = []
        g = nx.DiGraph()
        for stm in prg:
            if stm.ast_type == ASTType.Rule:
                heads = positive_head_predicates(stm)
                bodies = positive_body_predicates(stm)
                g.add_edges_from(product(bodies, heads))
                self.sccs = list(nx.strongly_connected_components(g))

    # returns true if all of the predicates in predlist have a positive dependency with each other
    def are_dependent(self, predlist):
        spl = set(predlist)
        for scc in self.sccs:
            if spl <= scc:
                return True
        return False
