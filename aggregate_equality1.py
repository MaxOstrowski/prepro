"""
 This module replaces bodys with aggregates of the form X = #agg{}
 and other literals of the form lb < X < ub with the direct replacement
 lb < #agg{} < ub
"""
from itertools import product

from clingo.ast import (
    ASTType,
    Comparison,
    ComparisonOperator,
    Guard,
    Literal,
    Location,
    Position,
    Sign,
    Transformer,
)

from dependency import PositivePredicateDependency, positive_predicates


def reverse_comparison(cmp):
    """reverse clingo.ast.ComparisonOperator"""
    return {
        ComparisonOperator.Equal: ComparisonOperator.NotEqual,
        ComparisonOperator.NotEqual: ComparisonOperator.Equal,
        ComparisonOperator.GreaterEqual: ComparisonOperator.LessEqual,
        ComparisonOperator.LessEqual: ComparisonOperator.GreaterEqual,
        ComparisonOperator.GreaterThan: ComparisonOperator.LessThan,
        ComparisonOperator.LessThan: ComparisonOperator.GreaterThan,
    }[cmp]


class BodyAggAnalytics:
    """class to analyze a body aggregate and capture its bounds"""

    def __init__(self, node):
        assert node.ast_type == ASTType.BodyAggregate
        self.equal_bound = None
        self.two_equals = False
        self.bounds = []  # all non equal bounds as right guards

        if node.left_guard and node.left_guard.ast_type == ASTType.Guard:
            guard = node.left_guard
            if (
                guard.comparison == ComparisonOperator.Equal
                and guard.term.ast_type == ASTType.Variable
            ):
                self.equal_bound = guard.term.name
            else:
                self.bounds.append(
                    guard.update(comparison=reverse_comparison(guard.comparison))
                )

        if node.right_guard and node.right_guard.ast_type == ASTType.Guard:
            guard = node.right_guard
            if (
                guard.comparison == ComparisonOperator.Equal
                and guard.term.ast_type == ASTType.Variable
            ):
                if self.equal_bound is not None:
                    self.two_equals = True
                    return
                self.equal_bound = guard.term.name
            else:
                self.bounds.append(guard)


class __ContainsVariable(Transformer):
    """helper class for function contains_variable"""

    def __init__(self, name):
        self.__name = name
        self.contains_variable = False

    def visit_Variable(self, node):
        if node.name == self.__name:
            self.contains_variable = True
        return node


def contains_variable(name, stm):
    """returns true if an AST contains a variable "name" """
    checker = __ContainsVariable(name)
    checker.visit(stm)
    return checker.contains_variable


class __ContainsInterval(Transformer):
    """helper class for function contains_interval"""

    def __init__(self):
        self.contains_interval = False

    def visit_Interval(self, node):
        self.contains_interval = True
        return node


def contains_interval(stm):
    """returns true if an AST contains am variable "clingo.ast.Interval" """
    checker = __ContainsInterval()
    checker.visit(stm)
    return checker.contains_interval


class BoundComputer:
    """class to find all bound restrictions of a variable varname"""

    def __init__(self, varname):
        self.varname = varname
        self.too_complicated = False
        self.bounds = []
        self.rest = []

    def __create_ordered_comparison(self, lhs, op, rhs):
        if lhs.ast_type == ASTType.Variable and lhs.name == self.varname:
            self.bounds.append(Comparison(lhs, [Guard(op, rhs)]))
        elif rhs.ast_type == ASTType.Variable and rhs.name == self.varname:
            self.bounds.append(Comparison(rhs, [Guard(reverse_comparison(op), lhs)]))
        else:
            self.too_complicated = (
                True
                if contains_variable(self.varname, lhs)
                or contains_variable(self.varname, rhs)
                else self.too_complicated
            )
            pos = Position("<string>", 1, 1)
            loc = Location(pos, pos)
            self.rest.append(
                Literal(loc, Sign.NoSign, Comparison(lhs, [Guard(op, rhs)]))
            )

    def compute_bounds(self, literal):
        """
        compute self.bounds as bounds for varname from a given ast
        compute self.rest for all non bounds for varname from a given ast
        sets self.too_complicated to True if AST is too complicated to analyize
        but still contains variable varname
        """
        if not contains_variable(self.varname, literal):
            self.rest.append(literal)
            return

        if contains_interval(literal):
            self.too_complicated = True
            return

        if (
            literal.ast_type != ASTType.Literal
            or literal.atom.ast_type != ASTType.Comparison
        ):
            self.too_complicated = True
            return

        sign = literal.sign
        comp = literal.atom

        if sign != Sign.NoSign and len(comp.guards) > 1:
            self.too_complicated = True
            return

        if (
            comp.term.ast_type == ASTType.Variable
            and comp.term.name == self.varname
            and len(comp.guards) == 1
        ):
            if sign == Sign.Negation:
                newguard = comp.guards[0].update(
                    comparison=reverse_comparison(comp.guards[0].comparison)
                )
                comp = comp.update(guards=[newguard])
            self.bounds.append(comp)
        elif not contains_variable(self.varname, comp.term) and len(comp.guards) == 1:
            guard = comp.guards[0]
            if (
                guard.term.ast_type == ASTType.Variable
                and guard.term.name == self.varname
            ):
                newcomparison = (
                    guard.comparison
                    if sign != Sign.NoSign
                    else reverse_comparison(guard.comparison)
                )
                comp = Comparison(guard.term, [Guard(newcomparison, comp.term)])
                self.bounds.append(comp)
            else:
                self.too_complicated = True
                return
        else:
            long_comp = []
            long_comp.append(comp.term)
            for guard in comp.guards:
                long_comp.append(guard.comparison)
                long_comp.append(guard.term)
            for i in range(0, len(long_comp) - 2, 2):
                lhs = long_comp[i]
                op = long_comp[i + 1]
                rhs = long_comp[i + 2]
                self.__create_ordered_comparison(lhs, op, rhs)
        return


# TODO: ensure no cycles though rule
class EqualVariable(Transformer):
    """
    replaces bodys with aggregates of the form X = #agg{}
    and other literals of the form lb < X < ub with the direct replacement
    lb < #agg{} < ub
    """

    # TODO: can't replace multiple aggregates at the same time yet, needs a fixpoint calculation

    def __init__(self, dependency):
        self.dependency = dependency

    def visit_Rule(self, node):
        assert node.ast_type == ASTType.Rule
        pheads = positive_predicates(node.head)
        analytics = {}
        for i, blit in enumerate(node.body):
            assert blit.ast_type == ASTType.Literal
            if blit.atom.ast_type == ASTType.BodyAggregate:
                agg_info = BodyAggAnalytics(blit.atom)
                if agg_info.equal_bound is not None and not agg_info.two_equals:
                    analytics[i] = agg_info
        for i, agg_info in analytics.items():
            if contains_variable(agg_info.equal_bound, node.head):
                continue
            cont = False
            pbodies = positive_predicates(node.body[i].atom)
            for head, body in product(pheads, pbodies):
                if self.dependency.are_dependent([head, body]):
                    cont = True
                    break
            if cont:
                continue
            bcomp = BoundComputer(agg_info.equal_bound)
            for key, blit in enumerate(node.body):
                if key == i:
                    continue
                bcomp.compute_bounds(blit)
            if not bcomp.too_complicated:
                bcomp.bounds = [b.guards[0] for b in bcomp.bounds]
                bcomp.bounds.extend(agg_info.bounds)
                if len(bcomp.bounds) <= 2:
                    sign = node.body[i].sign  # currently not used, this is wrong
                    agg = node.body[i].atom
                    agg = agg.update(left_guard=None, right_guard=None)
                    if len(bcomp.bounds) >= 1:
                        agg = agg.update(
                            left_guard=bcomp.bounds[0].update(
                                comparison=reverse_comparison(
                                    bcomp.bounds[0].comparison
                                )
                            )
                        )
                    if len(bcomp.bounds) == 2:
                        agg = agg.update(right_guard=bcomp.bounds[1])
                    return node.update(
                        body=[node.body[i].update(atom=agg, sign=sign)] + bcomp.rest
                    )
        return node
