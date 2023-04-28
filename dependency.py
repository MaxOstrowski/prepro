"""
A module for all predicate dependencies in the AST
"""
from itertools import product, chain
from collections import defaultdict

import networkx as nx
from clingo.ast import ASTType, Sign

from utils import collect_ast, contains_variable

from pprint import pprint

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
    """ converts ast Literal into (sign, name, arity) if sign is in signs"""
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
        self._no_domain = set()
        self._cycle_free_pdg = None
        prg = list(prg)
        self.domains = {} # key = ("p",3) -> ("dom",3)
        self.__compute_domain_predicates(prg)
        self.__compute_domains(prg)

    def __compute_domain_predicates(self, prg):
        g = nx.DiGraph()
        SIGNS = {Sign.NoSign, Sign.Negation, Sign.DoubleNegation}
        for stm in prg:
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
        self._cycle_free_pdg = g.copy()
        ### remove predicates in cycles
        for scc in nx.strongly_connected_components(g):
            if len(scc) > 1:
                self._no_domain.update(scc)
                self._cycle_free_pdg.remove_nodes_from(scc)
        for scc in nx.selfloop_edges(g):
            self._no_domain.add(scc[0])
            self._cycle_free_pdg.remove_nodes_from([scc[0]])

        ### remove predicates derived by using non_domain predicates
        for node in nx.topological_sort(self._cycle_free_pdg):
            for pre in g.predecessors(node):
                if pre in self._no_domain:
                    self._no_domain.add(node)
                    continue

    def is_domain(self, pred):
        """ pred = (name, arity)
            returns true if predicate can be computed statically
        """
        return pred not in self._no_domain
    

    def has_domain(self, pred):
        """ pred = (name, arity)
            returns true if a domain of pred has been computed
        """
        return self.is_domain(pred) or pred in self.domains
    
    
    def domain(self, pred):
        """ pred = (name, arity)
            returns ast of domain predicate of pred
        """
        assert(self.has_domain(pred))
        if self.is_domain(pred):
            return pred
        return self.domains[pred]
    

    # important TODO: not only collect all possible inferences for domains but mark predicates that are not possible to compute domain for
    def __compute_domains(self, prg):
        domain_rules = defaultdict(list) # atom -> [conditions, ...]
        for rule in prg:
            if rule.ast_type == ASTType.Rule:
                head = rule.head
                body = rule.body
                if head.ast_type == ASTType.Literal and head.sign == Sign.NoSign:
                    domain_rules[head.atom].append(body)
                elif head.ast_type == ASTType.Disjunction:
                    for elem in head.elements:
                        assert elem.ast_type == ASTType.ConditionalLiteral
                        condition = elem.condition
                        if elem.literal.sign == Sign.NoSign:
                            domain_rules[elem.literal.atom].append(chain(condition, body))
                elif head.ast_type == ASTType.HeadAggregate:
                    for elem in head.elements:
                        assert elem.condition.literal.sign == Sign.NoSign
                        domain_rules[elem.condition.literal.atom].append(chain(elem.condition, body))
                elif head.ast_type == ASTType.Aggregate:
                    for elem in head.elements:
                        assert elem.literal.sign == Sign.NoSign
                        domain_rules[elem.literal.atom].append(chain(elem.condition, body))

        for head in domain_rules.keys():
            assert head.ast_type == ASTType.SymbolicAtom
            # I actually need the position and maybe subreferencing of the variables if head(f(X), X) :- body
            head_variables = collect_ast(head, "Variables")

            def contains_head_var(cond):
                return any(map(lambda hv : contains_variable(hv, cond), head_variables))

            # TODO: maybe remove list and use generator
            domain_rules[head] = [list(filter(contains_head_var, conditions)) for conditions in domain_rules[head]]

        # for head in domain_rules.keys():
        #     #def have_domain(literals):
        #         #do visit SymbolicAtoms
        #     #             if lit.sign in signs and lit.atom.ast_type == ASTType.SymbolicAtom:
        #     # atom = lit.atom
        #     # if atom.symbol.ast_type == ASTType.Function:
        #     #     yield (lit.sign, atom.symbol.name, len(atom.symbol.arguments))

        #     for conditions in domain_rules[head]:
        #         if all(conditions, have_domain):
        #             print("yeah")
            
        # #if all predicates of a condition have a domain, replace all of them with their respective domain predicates
        #     #also a domain for a predicate is only finished if all rules with this head predicate have been evaluated

        pprint(domain_rules)

        #how to actually represent a domain_rules
        #- using ast ? Then I need to find the correct variables
        #p(A,B) -> dom(A,B) where dom(X,Y) is domain of p/2
        #what about p(f(A), A+B): easy -> dom(f(A), A+B)

        #what if the domain predicate is not dom(X,Y) but dom(f(X), X+Y, 42)
        #well, its still dom/3 as an overapproximation
        #Fazit: I will represent domains as dom/3
                        
                    #check if cond is a predicate and domain
                    #check if it contains variables of head


                            

