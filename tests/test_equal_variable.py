import pytest
from clingo.ast import Transformer, parse_string

from aggregate_equality1 import BoundComputer, EqualVariable
from dependency import PositivePredicateDependency


class RunBoundComputer(Transformer):
    def __init__(self):
        self.cbounds = set()
        self.crest = set()
        self.too_complicated = False

    def visit_Rule(self, rule):
        bc = BoundComputer("X")
        for node in rule.body:
            bc.compute_bounds(node)
            self.cbounds.update([str(b) for b in bc.bounds])
            self.crest.update([str(b) for b in bc.rest])
            self.too_complicated = True if bc.too_complicated else self.too_complicated
        return rule


@pytest.mark.parametrize(
    "rule, bounds, rest",
    [
        (":- X < 2.", ["X < 2"], []),
        (":- not X < 2.", ["X > 2"], []),
        (":- X = 2.", ["X = 2"], []),
        (":- not X = 2.", ["X != 2"], []),
        (":- X < 2, X > 4.", ["X < 2", "X > 4"], []),
        (":- 2 < X.", ["X > 2"], []),
        (":- not 2 < X.", ["X < 2"], []),
        (":- not 2 < X, X > 4.", ["X < 2", "X > 4"], []),
        (":- 2 < X < 4.", ["X > 2", "X < 4"], []),
        (":- 2 < X < 4 < Y < Z + 123.", ["X > 2", "X < 4"], ["4 < Y", "Y < (Z+123)"]),
        (
            ":- 2 < X, 1 < 4 < Y < Z + 123, f(Y).",
            ["X > 2"],
            ["1 < 4 < Y < (Z+123)", "f(Y)"],
        ),
    ],
)
def test_bound_computation(rule, bounds, rest):
    t = RunBoundComputer()
    parse_string(rule, lambda stm: t(stm))
    assert set(bounds) == t.cbounds
    assert set(rest) == t.crest
    assert not t.too_complicated


@pytest.mark.parametrize(
    "rule",
    [
        ":- not 1 < X < 2.",
        ":- 1 < X+1 < 2.",
        ":- f(X).",
        ":- X = 1..7.",
    ],
)
def test_toocomplicated_bounds(rule):
    t = RunBoundComputer()
    parse_string(rule, lambda stm: t(stm))
    assert t.too_complicated


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "#false :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.",
            "#false :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; X = #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; X >= 2; 5 > 3; X = Y; 1 <= X != 4 < 5.",
        ),
        (
            "#false :- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.",
            "#false :- 2 <= #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; 2 > 1; 5 > 3.",
        ),
        (
            "#false :- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, not X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.",
            "#false :- not 2 <= #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; 2 > 1; 5 > 3.",
        ),
    ],
)
def test_equal_variable(rule, result):
    prg = []
    parse_string(rule, lambda stm: prg.append(stm))
    pdg = PositivePredicateDependency(prg)
    eq = EqualVariable(pdg)

    class RuleVisitor(Transformer):
        def visit_Rule(self, stm):
            assert str(stm) == result
            return stm

    ruler = RuleVisitor()
    parse_string(rule, lambda stm: ruler(eq(stm)))


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "p(X) :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.",
            "p(X) :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; X = #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; X >= 2; 5 > 3; X = Y; 1 <= X != 4 < 5.",
        ),
        (
            "e :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2.",
            "e :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2; X = #sum { 1,e: e; 1,f: f; 1,g: g } <= 3; X >= 2.",
        ),
    ],
)
def test_equal_variable_reject(rule, result):
    prg = []
    parse_string(rule, lambda stm: prg.append(stm))
    pdg = PositivePredicateDependency(prg)
    eq = EqualVariable(pdg)

    class RuleVisitor(Transformer):
        def visit_Rule(self, stm):
            assert str(stm) == result
            return stm

    ruler = RuleVisitor()
    parse_string(rule, lambda stm: ruler(eq(stm)))
