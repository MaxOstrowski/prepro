from clingo.ast import parse_files, Transformer, ASTType, ComparisonOperator, parse_string, Sign, Comparison, Guard, Literal, Position, Location
from clingox.pprint import pprint, pformat

def reverse_comparison(cmp):
    m = {
        ComparisonOperator.Equal : ComparisonOperator.NotEqual,
        ComparisonOperator.NotEqual : ComparisonOperator.Equal,
        ComparisonOperator.GreaterEqual : ComparisonOperator.LessEqual,
        ComparisonOperator.LessEqual : ComparisonOperator.GreaterEqual,
        ComparisonOperator.GreaterThan : ComparisonOperator.LessThan,
        ComparisonOperator.LessThan : ComparisonOperator.GreaterThan,
    }
    return m[cmp]

class BodyAggAnalytics:
    def __init__(self, node):
        assert(node.ast_type == ASTType.BodyAggregate)
        self.equal_bound = None
        self.two_equals = False
        self.bounds = [] # all non equal bounds as right guards

        if node.left_guard and node.left_guard.ast_type == ASTType.Guard:
            guard = node.left_guard
            if guard.comparison == ComparisonOperator.Equal and guard.term.ast_type == ASTType.Variable:
                self.equal_bound = guard.term.name
            else:
                self.bounds.append(guard.update(comparison = reverse_comparison(guard.comparison)))

        if node.right_guard and node.right_guard.ast_type == ASTType.Guard:
            guard = node.right_guard
            if guard.comparison == ComparisonOperator.Equal and guard.term.ast_type == ASTType.Variable:
                if self.equal_bound is not None:
                    self.two_equals = True
                    return
                self.equal_bound = guard.term.name
            else:
                self.bounds.append(guard)


class ContainsVariable(Transformer):
    def __init__(self, name):
        self.__name = name
        self.contains_variable = False

    def visit_Variable(self, node):
        if node.name == self.__name:
            self.contains_variable = True
        return node

def contains_variable(name, stm):
    checker = ContainsVariable(name)
    checker.visit(stm)
    return checker.contains_variable


class ContainsInterval(Transformer):
    def __init__(self):
        self.contains_interval = False

    def visit_Interval(self, node):
        self.contains_interval = True
        return node

def contains_interval(stm):
    checker = ContainsInterval()
    checker.visit(stm)
    return checker.contains_interval


class BoundComputer:
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
            self.too_complicated = True if contains_variable(self.varname, lhs) or contains_variable(self.varname, rhs) else self.too_complicated
            pos = Position('<string>', 1, 1)
            loc = Location(pos, pos)
            self.rest.append(Literal(loc, Sign.NoSign, Comparison(lhs, [Guard(op, rhs)])))
        
    # compute ast.Comparisons for varname from a given ast
    def compute_bounds(self, literal):
        if not contains_variable(self.varname, literal):
            self.rest.append(literal)
            return
        
        if contains_interval(literal):
            self.too_complicated = True
            return
        
        if literal.ast_type != ASTType.Literal or literal.atom.ast_type != ASTType.Comparison:
            self.too_complicated = True
            return
        
        sign = literal.sign
        comp = literal.atom

        if sign != Sign.NoSign and len(comp.guards)>1:
            self.too_complicated = True
            return

        if comp.term.ast_type == ASTType.Variable and comp.term.name == self.varname and len(comp.guards)==1:
            if sign == Sign.Negation:
                newguard = comp.guards[0].update(comparison = reverse_comparison(comp.guards[0].comparison))
                comp = comp.update(guards = [newguard])
            self.bounds.append(comp)
        elif not contains_variable(self.varname, comp.term) and len(comp.guards)==1:
            guard = comp.guards[0]
            if guard.term.ast_type == ASTType.Variable and guard.term.name == self.varname:
                newcomparison = guard.comparison if sign != Sign.NoSign else reverse_comparison(guard.comparison)
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
            for i in range(0,len(long_comp)-2,2):
                lhs = long_comp[i]
                op = long_comp[i+1]
                rhs = long_comp[i+2]
                self.__create_ordered_comparison(lhs, op, rhs)
        return


# TODO: ensure no cycles though rule
class EqualVariable(Transformer):
    def visit_Rule(self, node):
        print(node)
        assert(node.ast_type == ASTType.Rule)
        analytics = {}
        for i, b in enumerate(node.body):
            assert(b.ast_type == ASTType.Literal)
            if b.atom.ast_type == ASTType.BodyAggregate:
                ba = BodyAggAnalytics(b.atom)
                if ba.equal_bound is not None and not ba.two_equals:
                    analytics[i] = ba
        for i, a in analytics.items():
            valid = True
            bc = BoundComputer(a.equal_bound)
            for key, b in enumerate(node.body):
                if key == i:
                    continue
                bc.compute_bounds(b)
            if not bc.too_complicated:
                bc.bounds = [b.guards[0] for b in bc.bounds]
                bc.bounds.extend(a.bounds)
                if len(bc.bounds) <= 2:
                    sign = node.body[i].sign # currently not used, this is wrong
                    agg = node.body[i].atom
                    agg = agg.update(left_guard=None, right_guard=None)
                    if len(bc.bounds) >= 1:
                        agg = agg.update(left_guard=bc.bounds[0].update(comparison=reverse_comparison(bc.bounds[0].comparison)))
                    if len(bc.bounds) == 2:
                        agg = agg.update(right_guard=bc.bounds[1])
                    return node.update(body=[agg] + bc.rest)
        return node

eq = EqualVariable()
parse_files(["test.lp"], lambda stm: print(eq(stm)))
