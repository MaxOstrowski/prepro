"""
 This module replaces bodys with aggregates of the form X = #max/min{}
 with an order encoding.
 Might also replace the usage of the resulting predicate with the order literals.
"""

from itertools import chain

from clingo.ast import AggregateFunction, ASTType, Transformer

from dependency import DomainPredicates
from utils import collect_ast


class MinMaxAggregator(Transformer):
    def __init__(self, prg, domain_predicates):
        self.domain_predicates = domain_predicates

    def execute(self, prg):
        ret = []
        for rule in prg:
            if rule.ast_type != ASTType.Rule:
                ret.append(rule)
                continue

            agg = None
            for blit in rule.body:
                if blit.ast_type == ASTType.Literal:
                    atom = blit.atom
                    if (
                        atom.ast_type == ASTType.BodyAggregate
                        and atom.function
                        in {
                            AggregateFunction.Max,
                            AggregateFunction.Min,
                        }
                        and len(atom.elements) == 1
                    ):  # TODO: lift this restriction, could add constants and other literals
                        agg = atom
            if agg is not None:
                inside_variables = set(
                    map(
                        lambda x: x.name,
                        chain(*map(lambda x: collect_ast(x, "Variable"), agg.elements)),
                    )
                )
                ### currently only support one element, but this is simply due to laziness of implementation
                elem = agg.elements[0]
                # collect all literals outside that aggregate that use the same variables
                lits_with_vars = []
                lits_without_vars = []
                for blit in rule.body:
                    if blit == agg:
                        continue
                    blit_vars = set(collect_ast(blit, "Variable"))
                    if len(blit_vars) > 0 and blit_vars <= inside_variables:
                        lits_with_vars.append(blit)
                    else:
                        lits_without_vars.append(blit)

            ret.append(rule)
        return ret
