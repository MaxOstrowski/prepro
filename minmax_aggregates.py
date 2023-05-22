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
    Comparison,
    ComparisonOperator,
    ConditionalLiteral,
    Function,
    Guard,
    Literal,
    Location,
    Position,
    Rule,
    Sign,
    SymbolicAtom,
    SymbolicTerm,
    Transformer,
    Variable,
)
from clingo.symbol import Infimum, Supremum

from dependency import DomainPredicates
from utils import BodyAggAnalytics, collect_ast


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
                        AggregateFunction.Min,
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
            in_and_outside_variables = (
                set()
            )  # variables that are used inside but also outside of the aggregate
            for blit in rule.body:
                if blit == agg:
                    continue
                blit_vars = set(map(lambda x: x.name, collect_ast(blit, "Variable")))
                if len(blit_vars) > 0 and blit_vars <= inside_variables:
                    in_and_outside_variables.update(
                        inside_variables.intersection(blit_vars)
                    )  # TODO: maybe fix an order
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

            # 1. create a new domain for the complete elem.condition + lits_with_vars
            

            direction = "min"
            if agg.atom.function == AggregateFunction.Max:
                direction = "max"    
            new_name = f"__{direction}_{number_of_aggregate}_{number_of_element}_{str(rule.location.begin.line)}"
            new_predicate = (new_name, 1)       


            head = SymbolicAtom(Function(loc, new_name, [weight], False))
            self.domain_predicates.add_domain_rule(
                head, [list(chain(elem.condition, lits_with_vars))]
            )
            if not self.domain_predicates.has_domain(new_predicate):
                return [rule]

            # 2. create dom and next predicates for it, and then use it to create chain with elem.condition + lits_with_vars
            ret = list(self.domain_predicates.create_domain(new_predicate))
            ret.extend(
                self.domain_predicates._create_nextpred_for_domain(new_predicate, 0)
            )

            minmax_pred = self.domain_predicates.max_predicate(new_predicate, 0)
            if agg.atom.function == AggregateFunction.Max:
                minmax_pred = self.domain_predicates.min_predicate(new_predicate, 0)

            
            chain_name = f"__chain_{direction}_{new_name}"
            next_pred = self.domain_predicates.next_predicate(new_predicate, 0)

            # TODO: think about the tuple used in the aggregate, its probably not correct to ignore it!
            rest_vars = sorted(
                [Variable(loc, name) for name in in_and_outside_variables]
            )
            aux_head = Literal(
                loc,
                Sign.NoSign,
                SymbolicAtom(Function(loc, chain_name, rest_vars + [weight], False)),
            )
            ret.append(Rule(loc, aux_head, list(chain(elem.condition, lits_with_vars))))

            prev = Variable(loc, "__PREV")
            next = Variable(loc, "__NEXT")
            body = []
            if agg.atom.function == AggregateFunction.Max:
                head = Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, chain_name, rest_vars + [prev], False)),
                )
                
                body.append(
                    Literal(
                        loc,
                        Sign.NoSign,
                        SymbolicAtom(Function(loc, chain_name, rest_vars + [next], False)),
                    )
                )
            else:
                head = Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, chain_name, rest_vars + [next], False)),
                )
                
                body.append(
                    Literal(
                        loc,
                        Sign.NoSign,
                        SymbolicAtom(Function(loc, chain_name, rest_vars + [prev], False)),
                    )
                )

            body.append(
                Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, next_pred[0], [prev, next], False)),
                )
            )
            ret.append(Rule(loc, head, body))

            # 3. create actual new max/min predicate
            if agg.atom.function == AggregateFunction.Max:
                head = Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, new_name, rest_vars + [prev], False)),
                )
            else:
                head = Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, new_name, rest_vars + [next], False)),
                )
            body = []
            if agg.atom.function == AggregateFunction.Max:
                body.append(
                    Literal(
                        loc,
                        Sign.NoSign,
                        SymbolicAtom(Function(loc, chain_name, rest_vars + [prev], False)),
                    )
                )
                body.append(
                    ConditionalLiteral(loc,
                    Literal(
                        loc,
                        Sign.Negation,
                        SymbolicAtom(Function(loc, chain_name, rest_vars + [next], False)),
                    ),
                    [
                    Literal(
                        loc,
                        Sign.NoSign,
                        SymbolicAtom(Function(loc, next_pred[0], [prev, next], False)),
                    )])
                )
            else:
                body.append(
                    Literal(
                        loc,
                        Sign.NoSign,
                        SymbolicAtom(Function(loc, chain_name, rest_vars + [next], False)),
                    )
                )
                body.append(
                    ConditionalLiteral(loc,
                    Literal(
                        loc,
                        Sign.Negation,
                        SymbolicAtom(Function(loc, chain_name, rest_vars + [prev], False)),
                    ),
                    [
                    Literal(
                        loc,
                        Sign.NoSign,
                        SymbolicAtom(Function(loc, next_pred[0], [prev, next], False)),
                    )])
                )
            ret.append(Rule(loc, head, body))

            if agg.atom.function == AggregateFunction.Max:
                head = Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(
                        Function(
                            loc, new_name, rest_vars + [SymbolicTerm(loc, Infimum)], False
                        )
                    ),
                )
            else:
                head = Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(
                        Function(
                            loc, new_name, rest_vars + [SymbolicTerm(loc, Supremum)], False
                        )
                    ),
                )
            body = []
            var_x = Variable(loc, "X")

            body.append(
                Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, minmax_pred[0], [var_x], False)),
                )
            )
            body.append(
                Literal(
                    loc,
                    Sign.Negation,
                    SymbolicAtom(Function(loc, chain_name, rest_vars + [var_x], False)),
                )
            )
            body.extend(lits_with_vars)
            ret.append(Rule(loc, head, body))

            # 3. replace original rule
            head = rule.head
            body = []

            analytics = BodyAggAnalytics(agg.atom)
            max_var = Variable(loc, f"__VAR{new_name}")
            if analytics.equal_variable_bound:
                max_var = Variable(loc, analytics.equal_variable_bound.pop(0))
            body.append(
                Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, new_name, rest_vars + [max_var], False)),
                )
            )
            # repair bounds
            if len(analytics.equal_variable_bound) == 1:
                body.append(
                    Literal(
                        loc,
                        Sign.NoSign,
                        Comparison(
                            max_var,
                            [
                                Guard(
                                    ComparisonOperator.Equal,
                                    Variable(loc, analytics.equal_variable_bound[0]),
                                )
                            ],
                        ),
                    )
                )
            for bound in analytics.bounds:
                body.append(Literal(loc, Sign.NoSign, Comparison(max_var, [bound])))
            body.extend(lits_without_vars)
            ret.append(Rule(loc, head, body))
            return ret

        return [rule]

    def execute(self, prg):
        ret = []
        for rule in prg:
            if rule.ast_type != ASTType.Rule:
                ret.append(rule)
                continue

            ret.extend(self._process_rule(rule))
        return ret
