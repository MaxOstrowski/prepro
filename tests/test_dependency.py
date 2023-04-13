import pytest
from clingo.ast import Transformer, parse_string

from dependency import (
    PositivePredicateDependency,
    positive_body_predicates,
    positive_head_predicates,
)


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "#false :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.",
            [("a", 0), ("b", 0), ("c", 0), ("e", 0), ("f", 0), ("g", 0)],
        ),
        (
            "#false :- 1 { a : e; b : not f; c } 2, d.",
            [("a", 0), ("b", 0), ("c", 0), ("d", 0), ("e", 0)],
        ),
    ],
)
def test_positive_body(rule, result):
    class RuleVisitor(Transformer):
        def visit_Rule(self, stm):
            assert set(positive_body_predicates(stm)) == set(result)
            return stm

    ruler = RuleVisitor()
    parse_string(rule, lambda stm: ruler((stm)))


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "a(1,4,f(4)).",
            [("a", 3)],
        ),
        (
            "1 <= #sum { 1,a: a; 1,b: b; 1: c } <= 2.",
            [("a", 0), ("b", 0), ("c", 0)],
        ),
        (
            "1 { a : e; b : not f; c } 2.",
            [("a", 0), ("b", 0), ("c", 0), ("e", 0)],
        ),
        (
            "a; b; not c.",
            [("a", 0), ("b", 0)],
        ),
        (
            "a : d; b : not e; not c.",
            [("a", 0), ("b", 0), ("d", 0)],
        ),
    ],
)
def test_positive_head(rule, result):
    class RuleVisitor(Transformer):
        def visit_Rule(self, stm):
            assert set(positive_head_predicates(stm)) == set(result)
            return stm

    ruler = RuleVisitor()
    parse_string(rule, lambda stm: ruler((stm)))


@pytest.mark.parametrize(
    "prg, result",
    [
        (
            """
            b :- a.
            c :- b.
            d :- c.
            a :- d.
            e :- d.
            """,
            [{("e", 0)}, {("a", 0), ("b", 0), ("c", 0), ("d", 0)}],
        ),
        (
            """
            b :- #sum{1 : a}.
            c :- b.
            {d} :- c, not d.
            a :- d, not e.
            e :- d.
            f;g :- e.
            e;not g :- f.
            e :- not g.
            """,
            [
                {("g", 0)},
                {("e", 0), ("f", 0)},
                {("a", 0), ("b", 0), ("c", 0), ("d", 0)},
            ],
        ),
    ],
)
def test_positive_dependencies(prg, result):
    ast = []
    parse_string(prg, lambda stm: ast.append((stm)))
    assert sorted(PositivePredicateDependency(ast).sccs) == sorted(result)
