from clingo.ast import  Transformer, parse_string
from main import BoundComputer
import pytest


class Trans(Transformer):
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

@pytest.mark.parametrize("rule, bounds, rest", [
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
    (":- 2 < X, 1 < 4 < Y < Z + 123, f(Y).", ["X > 2"], ["1 < 4 < Y < (Z+123)", "f(Y)"]),
    ])
def test_bound_computation(rule, bounds, rest):
    t = Trans()
    parse_string(rule, lambda stm: t(stm))
    assert set(bounds) == t.cbounds
    assert set(rest) == t.crest
    assert not t.too_complicated

@pytest.mark.parametrize("rule", [
    ":- not 1 < X < 2.",
    ":- 1 < X+1 < 2.",
    ":- f(X).",
    ":- X = 1..7.",
    ])
def test_toocomplicated_bounds(rule):
    t = Trans()
    parse_string(rule, lambda stm: t(stm))
    assert t.too_complicated