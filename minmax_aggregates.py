"""
 This module replaces bodys with aggregates of the form X = #max/min{}
 with an order encoding.
 Might also replace the usage of the resulting predicate with the order literals.
"""

from itertools import chain

from clingo.ast import (
    Aggregate,
    AggregateFunction,
    ASTType,
    ConditionalLiteral,
    Function,
    Literal,
    Location,
    Position,
    Rule,
    Sign,
    SymbolicAtom,
    Transformer,
)

from dependency import DomainPredicates
from utils import collect_ast


class MinMaxAggregator(Transformer):
    def __init__(self, prg, domain_predicates):
        self.domain_predicates = domain_predicates

    def _process_rule(self, rule):
        """returns a list of rules to replace this rule"""
        agg = None
        for blit in rule.body:
            if blit.ast_type == ASTType.Literal:
                atom = blit.atom
                if (
                    atom.ast_type == ASTType.BodyAggregate
                    and atom.function
                    in {
                        AggregateFunction.Max,
                        # AggregateFunction.Min, # TODO: add min Agg
                    }
                    and len(atom.elements)
                    == 1  # TODO: lift this restriction, could add constants and other literals
                    and agg
                    == None  # TODO: lift this restriction, could have more than one agg, but the number needs to go into the chain name
                ):
                    agg = blit
        if agg is not None:
            inside_variables = set(
                map(
                    lambda x: x.name,
                    chain(
                        *map(lambda x: collect_ast(x, "Variable"), agg.atom.elements)
                    ),
                )
            )
            ### currently only support one element, but this is simply due to laziness of implementation
            elem = agg.atom.elements[
                0
            ]  # TODO: also number of which element needs to go into the chain name
            # collect all literals outside that aggregate that use the same variables
            lits_with_vars = []
            lits_without_vars = []
            for blit in rule.body:
                if blit == agg:
                    continue
                blit_vars = set(map(lambda x: x.name, collect_ast(blit, "Variable")))
                if len(blit_vars) > 0 and blit_vars <= inside_variables:
                    lits_with_vars.append(blit)
                else:
                    lits_without_vars.append(blit)

            if (
                len(elem.condition) > 1
            ):  # TODO: create a new domain if several conditions are used, also create next for this domain
                return [rule]
            if (
                elem.condition[0].ast_type != ASTType.Literal
                or elem.condition[0].atom.ast_type != ASTType.SymbolicAtom
            ):  # TODO: lift restrictions, currently only needed to get some domain
                return [rule]

            condition_pred = (
                elem.condition[0].atom.symbol.name,
                len(elem.condition[0].atom.symbol.arguments),
            )
            if not self.domain_predicates.has_domain(condition_pred):
                return [rule]

            pos = Position("<string>", 1, 1)
            loc = Location(pos, pos)
            number_of_aggregate = 0
            number_of_element = 0
            weight = elem.terms[0]
            new_name = f"__aux_{number_of_aggregate}_{number_of_element}_{str(rule.location.begin.line)}"
            new_predicate = (new_name, 1)
            head = SymbolicAtom(Function(loc, new_name, [weight], False))
            self.domain_predicates.add_domain_rule(
                head, [list(chain(elem.condition, lits_with_vars))]
            )
            if not self.domain_predicates.has_domain(new_predicate):
                return [rule]
            # 1. create a new domain for the complete elem.condition + lits_with_vars
            ret = list(self.domain_predicates.create_domain(new_predicate))
            ret.extend(
                self.domain_predicates._create_nextpred_for_domain(new_predicate, 0)
            )
            ret.append(rule)
            return ret

            # 2. create dom and next predicates for it, and then use it to create chain with elem.condition + lits_with_vars
            # new domain is unary

            # next_pred = self.domain_predicates.next_predicate(condition_pred, position)

            # chain_name = f"__chain_down_{number_of_aggregate}_{number_of_element}{next_pred[0]}"
            # print(chain_name)
        return [rule]

    def execute(self, prg):
        ret = []
        for rule in prg:
            if rule.ast_type != ASTType.Rule:
                ret.append(rule)
                continue

            ret.extend(self._process_rule(rule))
        return ret
