"""
 This module replaces bodys with aggregates of the form X = #max/min{}
 with an order encoding.
 Might also replace the usage of the resulting predicate with the order literals.
"""

from collections import defaultdict
from itertools import chain

from clingo.ast import (
    AggregateFunction,
    ASTType,
    BinaryOperation,
    BinaryOperator,
    BodyAggregate,
    BodyAggregateElement,
    Comparison,
    ComparisonOperator,
    ConditionalLiteral,
    Function,
    Guard,
    Literal,
    Location,
    Minimize,
    Position,
    Rule,
    Sign,
    SymbolicAtom,
    SymbolicTerm,
    Transformer,
    UnaryOperation,
    UnaryOperator,
    Variable,
)
from clingo.symbol import Infimum, Supremum

from dependency import DOM_STR
from utils import BodyAggAnalytics, collect_ast, potentially_unifying, predicates

CHAIN_STR = "__chain"
pos = Position("<string>", 1, 1)
loc = Location(pos, pos)
NEXT = Variable(loc, "__NEXT")
PREV = Variable(loc, "__PREV")


def _characteristic_variables(term):
    """yield all characteristic variable names of the given Term,
    this means all Variables not occuring in arithmetics, bounds, etc...
    Assumes term is unpooled.
    """

    if term.ast_type in {ASTType.Variable, ASTType.SymbolicTerm}:
        yield from collect_ast(term, "Variable")
    elif term.ast_type == ASTType.Function:
        for i in term.arguments:
            yield from _characteristic_variables(i)


class MinMaxAggregator:
    """Translates some min/max aggregates into chains"""

    class Translation:
        """translates an old predicate to a new one"""

        def __init__(self, oldpred, newpred, mapping):
            self.oldpred = oldpred
            self.newpred = newpred
            # simple ordered list of indices or none, to map f(A1,A2,A4) to b(A1,A4,A3,A2)
            # have mapping [0,3,1], reverse mapping would be [0,2,None,1]
            self.mapping = mapping

        def translate_parameters(self, arguments):
            """given the mapping, return the mapped order of the argument terms"""
            ret = []
            for oldidx, index in enumerate(self.mapping):
                if index == None:
                    continue
                assert len(arguments) > index
                if index >= len(ret):
                    ret.extend([None] * (index + 1 - len(ret)))
                ret[index] = arguments[oldidx]
            return ret

    def __init__(self, rule_dependency, domain_predicates):
        self.rule_dependency = rule_dependency
        self.domain_predicates = domain_predicates
        # list of ({AggregateFunction.Max, AggregateFunction.Min}, (name,arity), index)
        #  where index is the position of the variable indicating the minimum/maximum
        self._minmax_preds = []

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
                    and len(atom.elements) == 1  # TODO: lift this restriction, could add constants and other literals
                    and agg
                    is None  # TODO: lift this restriction, could have more than one agg, but the number needs to go into the chain name
                ):
                    agg = blit
        if agg is not None:
            inside_variables = set(
                map(
                    lambda x: x.name,
                    chain(*map(lambda x: collect_ast(x, "Variable"), agg.atom.elements)),
                )
            )
            ### currently only support one element, but this is simply due to laziness of implementation
            elem = agg.atom.elements[0]  # TODO: also number of which element needs to go into the chain name
            # collect all literals outside that aggregate that use the same variables
            lits_with_vars = []
            lits_without_vars = []
            in_and_outside_variables = set()  # variables that are used inside but also outside of the aggregate
            for blit in rule.body:
                if blit == agg:
                    continue
                blit_vars = set(map(lambda x: x.name, collect_ast(blit, "Variable")))
                if len(blit_vars) > 0 and blit_vars <= inside_variables:
                    in_and_outside_variables.update(inside_variables.intersection(blit_vars))
                    lits_with_vars.append(blit)
                else:
                    lits_without_vars.append(blit)

            if (
                len(elem.condition) > 1
            ):  # TODO: create a new domain if several conditions are used, also create next_ for this domain
                return [rule]
            if (
                elem.condition[0].ast_type != ASTType.Literal or elem.condition[0].atom.ast_type != ASTType.SymbolicAtom
            ):  # TODO: lift restrictions, currently only needed to get some domain
                return [rule]

            condition_pred = (
                elem.condition[0].atom.symbol.name,
                len(elem.condition[0].atom.symbol.arguments),
            )
            if not self.domain_predicates.has_domain(condition_pred) or self.domain_predicates.is_static(
                condition_pred
            ):
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
            self.domain_predicates.add_domain_rule(head, [list(chain(elem.condition, lits_with_vars))])
            if not self.domain_predicates.has_domain(new_predicate):
                return [rule]

            # 2. create dom and next_ predicates for it, and then use it to
            # create chain with elem.condition + lits_with_vars
            ret = list(self.domain_predicates.create_domain(new_predicate))
            ret.extend(self.domain_predicates._create_nextpred_for_domain(new_predicate, 0))

            minmax_pred = self.domain_predicates.max_predicate(new_predicate, 0)
            if agg.atom.function == AggregateFunction.Max:
                minmax_pred = self.domain_predicates.min_predicate(new_predicate, 0)

            chain_name = f"{CHAIN_STR}{new_name}"
            next_pred = self.domain_predicates.next_predicate(new_predicate, 0)

            rest_vars = sorted([Variable(loc, name) for name in in_and_outside_variables])
            aux_head = Literal(
                loc,
                Sign.NoSign,
                SymbolicAtom(Function(loc, chain_name, rest_vars + [weight], False)),
            )
            ret.append(Rule(loc, aux_head, list(chain(elem.condition, lits_with_vars))))

            prev = Variable(loc, "__PREV")
            next_ = Variable(loc, "__NEXT")

            prev_agg = next_
            next_agg = prev
            if agg.atom.function == AggregateFunction.Max:
                prev_agg = prev
                next_agg = next_

            head = Literal(
                loc,
                Sign.NoSign,
                SymbolicAtom(Function(loc, chain_name, rest_vars + [prev_agg], False)),
            )

            body = []
            body.append(
                Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, chain_name, rest_vars + [next_agg], False)),
                )
            )
            body.append(
                Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, next_pred[0], [prev, next_], False)),
                )
            )
            ret.append(Rule(loc, head, body))

            # 3. create actual new max/min predicate
            head = Literal(
                loc,
                Sign.NoSign,
                SymbolicAtom(Function(loc, new_name, rest_vars + [prev_agg], False)),
            )

            body = []
            body.append(
                Literal(
                    loc,
                    Sign.NoSign,
                    SymbolicAtom(Function(loc, chain_name, rest_vars + [prev_agg], False)),
                )
            )
            body.append(
                ConditionalLiteral(
                    loc,
                    Literal(
                        loc,
                        Sign.Negation,
                        SymbolicAtom(Function(loc, chain_name, rest_vars + [next_agg], False)),
                    ),
                    [
                        Literal(
                            loc,
                            Sign.NoSign,
                            SymbolicAtom(Function(loc, next_pred[0], [prev, next_], False)),
                        )
                    ],
                )
            )
            ret.append(Rule(loc, head, body))

            border = Supremum
            if agg.atom.function == AggregateFunction.Max:
                border = Infimum

            head = Literal(
                loc,
                Sign.NoSign,
                SymbolicAtom(Function(loc, new_name, rest_vars + [SymbolicTerm(loc, border)], False)),
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

            if not (
                head.ast_type == ASTType.Literal
                and head.atom.ast_type == ASTType.SymbolicAtom
                and head.atom.symbol.ast_type == ASTType.Function
                and len(self.rule_dependency.get_bodies((head.atom.symbol.name, len(head.atom.symbol.arguments))))
                == 1  # only this head occurence
            ):
                return ret
            symbol = head.atom.symbol
            for arg in symbol.arguments:
                if arg.ast_type not in {ASTType.Variable, ASTType.SymbolicTerm}:
                    return ret

            mapping = [
                (rest_vars + [max_var]).index(arg) if arg in rest_vars + [max_var] else None for arg in symbol.arguments
            ]

            translation = self.Translation(
                (symbol.name, len(symbol.arguments)),
                (new_name, len(rest_vars) + 1),
                mapping,
            )
            for i, arg in enumerate(symbol.arguments):
                if arg.ast_type == ASTType.Variable and arg.name == max_var.name:
                    self._minmax_preds.append((agg.atom.function, translation, i))

            return ret

        return [rule]

    def _replace_results_in_minimize(self, stm, minimizes):
        """
        return list of statements that replaces the minimize statement
        or returns the statement itself in a list
        """
        assert stm.ast_type == ASTType.Minimize
        ret = []

        term_tuple = (
            stm.weight,
            stm.priority,
            *stm.terms,
        )
        if stm.weight.ast_type == ASTType.Variable:
            varname = stm.weight.name
            minimize = True
        elif (
            stm.weight.ast_type == ASTType.UnaryOperation
            and stm.weight.operator_type == UnaryOperator.Minus
            and stm.weight.argument.ast_type == ASTType.Variable
        ):
            varname = stm.weight.argument.name
            minimize = False

        else:
            return [stm]

        l = set(chain.from_iterable(predicates(b, {Sign.NoSign, Sign.DoubleNegation}) for b in stm.body))
        l = [(x[1], x[2]) for x in l]
        temp_minmax_preds = []
        for aggtype, translation, idx in self._minmax_preds:
            if translation.oldpred in l:
                # check if it is globally safe to assume a unique tuple semantics
                def pot_unif(lhs, rhs):
                    if len(lhs) != len(rhs):
                        return False
                    return all(map(lambda x: potentially_unifying(*x), zip(lhs, rhs)))

                unsafe = []
                for terms, objective in minimizes.items():
                    if pot_unif(terms, term_tuple):
                        unsafe.extend([x for x in objective if x != stm])

                if not unsafe:
                    temp_minmax_preds.append((aggtype, translation, idx))

        if not temp_minmax_preds:
            return [stm]

        if minimize:

            def negate_if(x):
                return x

        else:

            def negate_if(x):
                return UnaryOperation(loc, UnaryOperator.Minus, x)

        for aggtype, translation, idx in temp_minmax_preds:
            if aggtype == AggregateFunction.Max:
                prev = PREV
                next_ = NEXT
            else:
                prev = NEXT
                next_ = PREV

            # (__NEXT-__PREV), __chain__max_0_0_x(__PREV,__NEXT) : __chain__max_0_0_x(P,__NEXT), __next_0__dom___max_0_0_11(__PREV,__NEXT)
            weight = negate_if(BinaryOperation(loc, BinaryOperator.Minus, next_, prev))
            priority = stm.priority
            newpred = translation.newpred
            chain_name = f"{CHAIN_STR}{newpred[0]}"
            terms = [Function(loc, chain_name, [PREV, NEXT], False)] + list(stm.terms)
            body = [
                b
                for b in stm.body
                if translation.newpred
                in set(
                    map(
                        lambda x: (x[1], x[2]),
                        chain.from_iterable(predicates(b, {Sign.NoSign}) for b in stm.body),
                    )
                )
            ]
            oldmax = [x for x in stm.body if x not in body][0]
            # check if all Variables from old predicate are used in the tuple identifier
            # to make a unique semantics
            old_vars = set(map(lambda x: x.name, collect_ast(oldmax, "Variable"))) - {varname}
            term_vars = chain.from_iterable(map(_characteristic_variables, term_tuple[2:]))
            term_vars = {x.name for x in term_vars}
            if not old_vars <= term_vars:
                ret.append(stm)
                continue
            newargs = translation.translate_parameters(oldmax.atom.symbol.arguments)
            newargs = [next_ if i == idx else x for i, x in enumerate(newargs)]
            chainpred = Literal(
                loc,
                Sign.NoSign,
                SymbolicAtom(Function(loc, chain_name, newargs, False)),
            )
            dompred = (f"{DOM_STR}{newpred[0]}", 1)
            nextpred = Literal(
                loc,
                Sign.NoSign,
                SymbolicAtom(
                    Function(
                        loc,
                        self.domain_predicates.next_predicate(dompred, 0)[0],
                        [PREV, NEXT],
                        False,
                    )
                ),
            )
            ret.append(Minimize(loc, weight, priority, terms, [chainpred, nextpred] + body))
            # __NEXT, __chain__max_0_0_x(#sup,__NEXT) : __chain__max_0_0_x(P,__NEXT), __min_0__dom___max_0_0_x(__NEXT)
            infsup = Infimum
            if aggtype == AggregateFunction.Max:
                infsup = Supremum
            weight = negate_if(next_)
            terms = [Function(loc, chain_name, [SymbolicTerm(loc, infsup), next_], False)] + list(stm.terms)
            if aggtype == AggregateFunction.Max:
                minmaxpred = self.domain_predicates.min_predicate(dompred, 0)[0]
            else:
                minmaxpred = self.domain_predicates.max_predicate(dompred, 0)[0]
            minmaxlit = Literal(
                loc,
                Sign.NoSign,
                SymbolicAtom(
                    Function(
                        loc,
                        minmaxpred,
                        [next_],
                        False,
                    )
                ),
            )
            ret.append(Minimize(loc, weight, priority, terms, [chainpred, minmaxlit] + body))
            # #inf and #sup are ignored by minimized and therefore not included
            # (also would require more complex variable bindings)
        return ret

    def _replace_results_in_sum(self, stm):
        """
        replaces min/max predicates in sum aggregates by returning a list of statements
        or the old statement if no replacement is possible
        """

        if stm.ast_type != ASTType.Rule:
            return [stm]
        body = []
        for b in stm.body:
            if (
                b.ast_type == ASTType.Literal
                and b.atom.ast_type == ASTType.BodyAggregate
                and b.atom.function in (AggregateFunction.Sum, AggregateFunction.SumPlus)
            ):
                # TODO: refactor same replace of chain literals inside minimize and sum constraits out
                atom = b.atom
                elements = []
                other_terms = {elem.terms: elem for elem in atom.elements}
                for elem in atom.elements:
                    term_tuple = elem.terms
                    if term_tuple[0].ast_type == ASTType.Variable:
                        varname = term_tuple[0].name
                        minimize = True  # TODO: find a better name
                    elif (
                        term_tuple[0].ast_type == ASTType.UnaryOperation
                        and term_tuple[0].operator_type == UnaryOperator.Minus
                        and term_tuple[0].argument.ast_type == ASTType.Variable
                    ):
                        varname = term_tuple[0].argument.name
                        minimize = False

                    else:
                        elements.append(elem)
                        continue
                    # collect all predicates in this condition in l
                    l = set(
                        chain.from_iterable(predicates(b, {Sign.NoSign, Sign.DoubleNegation}) for b in elem.condition)
                    )
                    l = [(x[1], x[2]) for x in l]
                    temp_minmax_preds = []
                    for aggtype, translation, idx in self._minmax_preds:
                        if translation.oldpred in l:
                            # check if it is locally safe to assume a unique tuple semantics
                            def pot_unif(lhs, rhs):
                                if len(lhs) != len(rhs):
                                    return False
                                return all(
                                    map(
                                        lambda x: potentially_unifying(*x),
                                        zip(lhs, rhs),
                                    )
                                )

                            unsafe = False
                            for other_elem in atom.elements:
                                if other_elem == elem:
                                    continue
                                if pot_unif(other_elem.terms, term_tuple):
                                    unsafe = True

                            if not unsafe:
                                temp_minmax_preds.append((aggtype, translation, idx))

                    if not temp_minmax_preds:
                        elements.append(elem)
                        continue

                    # TODO: still need to fill in element
                    if minimize:

                        def negate_if(x):
                            return x

                    else:

                        def negate_if(x):
                            return UnaryOperation(loc, UnaryOperator.Minus, x)

                    for aggtype, translation, idx in temp_minmax_preds:
                        if aggtype == AggregateFunction.Max:
                            prev = PREV
                            next_ = NEXT
                        else:
                            prev = NEXT
                            next_ = PREV

                        # (__NEXT-__PREV), __chain__max_0_0_x(__PREV,__NEXT) : __chain__max_0_0_x(P,__NEXT), __next_0__dom___max_0_0_11(__PREV,__NEXT)
                        weight = negate_if(BinaryOperation(loc, BinaryOperator.Minus, next_, prev))
                        newpred = translation.newpred
                        chain_name = f"{CHAIN_STR}{newpred[0]}"
                        terms = [Function(loc, chain_name, [PREV, NEXT], False)] + list(term_tuple[1:])
                        body = [
                            b
                            for b in elem.condition
                            if translation.newpred
                            in set(
                                map(
                                    lambda x: (x[1], x[2]),
                                    chain.from_iterable(predicates(b, {Sign.NoSign}) for b in elem.condition),
                                )
                            )
                        ]
                        oldmax = [x for x in elem.condition if x not in body][0]
                        # check if all Variables from old predicate are used in the tuple identifier
                        # to make a unique semantics
                        old_vars = set(map(lambda x: x.name, collect_ast(oldmax, "Variable"))) - {varname}
                        term_vars = chain.from_iterable(map(_characteristic_variables, term_tuple[1:]))
                        term_vars = {x.name for x in term_vars}
                        if not old_vars <= term_vars:
                            elements.append(elem)
                            continue
                        newargs = translation.translate_parameters(oldmax.atom.symbol.arguments)
                        newargs = [next_ if i == idx else x for i, x in enumerate(newargs)]
                        chainpred = Literal(
                            loc,
                            Sign.NoSign,
                            SymbolicAtom(Function(loc, chain_name, newargs, False)),
                        )
                        dompred = (f"{DOM_STR}{newpred[0]}", 1)
                        nextpred = Literal(
                            loc,
                            Sign.NoSign,
                            SymbolicAtom(
                                Function(
                                    loc,
                                    self.domain_predicates.next_predicate(dompred, 0)[0],
                                    [PREV, NEXT],
                                    False,
                                )
                            ),
                        )
                        elements.append(BodyAggregateElement([weight] + terms, [chainpred, nextpred] + body))
                        # __NEXT, __chain__max_0_0_x(#sup,__NEXT) : __chain__max_0_0_x(P,__NEXT), __min_0__dom___max_0_0_x(__NEXT)
                        infsup = Infimum
                        if aggtype == AggregateFunction.Max:
                            infsup = Supremum
                        weight = negate_if(next_)
                        terms = [
                            Function(
                                loc,
                                chain_name,
                                [SymbolicTerm(loc, infsup), next_],
                                False,
                            )
                        ] + list(term_tuple[1:])
                        if aggtype == AggregateFunction.Max:
                            minmaxpred = self.domain_predicates.min_predicate(dompred, 0)[0]
                        else:
                            minmaxpred = self.domain_predicates.max_predicate(dompred, 0)[0]
                        minmaxlit = Literal(
                            loc,
                            Sign.NoSign,
                            SymbolicAtom(
                                Function(
                                    loc,
                                    minmaxpred,
                                    [next_],
                                    False,
                                )
                            ),
                        )
                        elements.append(BodyAggregateElement([weight] + terms, [chainpred, minmaxlit] + body))
                        # #inf and #sup are ignored by minimized and therefore not included
                        # (also would require more complex variable bindings)

                agg = BodyAggregate(loc, atom.left_guard, atom.function, elements, atom.right_guard)
                body.append(Literal(loc, b.sign, agg))
            else:
                body.append(b)
        return [Rule(loc, stm.head, body)]

    def _replace_results_in_x(self, prg, minimizes):
        """
        replace all predicates that computed max/minimum values with their order encoding
        in sum contexts
        """
        ret = []
        for stm in prg:
            if stm.ast_type == ASTType.Minimize:
                ret.extend(self._replace_results_in_minimize(stm, minimizes))
            elif stm.ast_type == ASTType.Rule and any(
                map(
                    lambda body: body.ast_type == ASTType.Literal
                    and body.atom.ast_type == ASTType.BodyAggregate
                    and body.atom.function in (AggregateFunction.Sum, AggregateFunction.SumPlus),
                    stm.body,
                )
            ):
                ret.extend(self._replace_results_in_sum(stm))
            else:
                ret.append(stm)
                continue
        return ret

    def execute(self, prg):
        """
        replace easy min/max aggregates with chaining rules
        also replace the usage of the results in sum and optimize conditions
        """
        ret = []
        minimizes = defaultdict(list)
        for rule in prg:
            if rule.ast_type == ASTType.Minimize:
                minimizes[
                    (
                        rule.weight,
                        rule.priority,
                        *rule.terms,
                    )
                ].append(rule)

            if rule.ast_type != ASTType.Rule:
                ret.append(rule)
                continue

            ret.extend(self._process_rule(rule))
        ret = self._replace_results_in_x(ret, minimizes)
        return ret
