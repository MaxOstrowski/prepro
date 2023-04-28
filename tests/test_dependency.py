import pytest
from clingo.ast import Sign, Transformer, parse_string

from dependency import (
    DomainPredicates,
    PositivePredicateDependency,
    body_predicates,
    head_predicates,
)


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "#false :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.",
            [
                (Sign.NoSign, "a", 0),
                (Sign.NoSign, "b", 0),
                (Sign.NoSign, "c", 0),
                (Sign.NoSign, "e", 0),
                (Sign.NoSign, "f", 0),
                (Sign.NoSign, "g", 0),
            ],
        ),
        (
            "#false :- 1 { a : e; b : not f; c } 2, d.",
            [
                (Sign.NoSign, "a", 0),
                (Sign.NoSign, "b", 0),
                (Sign.NoSign, "c", 0),
                (Sign.NoSign, "d", 0),
                (Sign.NoSign, "e", 0),
            ],
        ),
    ],
)
def test_positive_body(rule, result):
    class RuleVisitor(Transformer):
        def visit_Rule(self, stm):
            assert set(body_predicates(stm, {Sign.NoSign})) == set(result)
            return stm

    ruler = RuleVisitor()
    parse_string(rule, lambda stm: ruler((stm)))


@pytest.mark.parametrize(
    "rule, result",
    [
        (
            "a(1,4,f(4)).",
            [(Sign.NoSign, "a", 3)],
        ),
        (
            "1 <= #sum { 1,a: a; 1,b: b; 1: c } <= 2.",
            [(Sign.NoSign, "a", 0), (Sign.NoSign, "b", 0), (Sign.NoSign, "c", 0)],
        ),
        (
            "1 { a : e; b : not f; c } 2.",
            [
                (Sign.NoSign, "a", 0),
                (Sign.NoSign, "b", 0),
                (Sign.NoSign, "c", 0),
                (Sign.NoSign, "e", 0),
            ],
        ),
        (
            "a; b; not c.",
            [(Sign.NoSign, "a", 0), (Sign.NoSign, "b", 0)],
        ),
        (
            "a : d; b : not e; not c.",
            [(Sign.NoSign, "a", 0), (Sign.NoSign, "b", 0), (Sign.NoSign, "d", 0)],
        ),
    ],
)
def test_positive_head(rule, result):
    class RuleVisitor(Transformer):
        def visit_Rule(self, stm):
            assert set(head_predicates(stm, {Sign.NoSign})) == set(result)
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


@pytest.mark.parametrize(
    "prg, domain, notdomain, hasdomain",
    [
        (
            """
            b :- a.
            c :- b.
            d :- c.
            a :- d.
            e :- d.
            """,
            [("x", 3)],
            [
                ("a", 0),
                ("b", 0),
                ("c", 0),
                ("d", 0),
                ("e", 0),
            ],
            [
                ("a", 0),
                ("b", 0),
                ("c", 0),
                ("d", 0),
                ("e", 0),
                ("x", 3),

            ],
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
            x :- not x.
            y.
            z :- y.
            {w}.
            u ; v.
            p(1) :- w.
            q(X) :- not p(X).
            """,
            [
                ("y", 0),
                ("z", 0),
            ],
            [
                ("a", 0),
                ("b", 0),
                ("c", 0),
                ("d", 0),
                ("e", 0),
                ("f", 0),
                ("g", 0),
                ("x", 0),
                ("w", 0),
                ("u", 0),
                ("v", 0),
                ("p", 1),
                ("q", 1),
            ],
            [
                ("y", 0),
                ("z", 0),
                ("a", 0),
                ("b", 0),
                ("c", 0),
                ("d", 0),
                ("e", 0),
                ("f", 0),
                ("g", 0),
                ("x", 0),
                ("w", 0),
                ("u", 0),
                ("v", 0),
                ("p", 1),
            ],
        ),
        (
            """
            a(X) :- b(X,Y), c(Y).
            {d(X)} :- b(X,Y), c(Y).
            """,
            [
                ("a", 1),
                ("b", 2),
                ("c", 1),
            ],
            [
                ("d", 1)
            ],
            [
                ("a", 1),
                ("b", 2),
                ("c", 1),
                ("d", 1),
            ],
        ),
    ],
)
def test_domain_predicates(prg, domain, notdomain, hasdomain):
    ast = []
    parse_string(prg, lambda stm: ast.append((stm)))
    dp = DomainPredicates(ast)
    for pred in domain:
        assert dp.is_domain(pred)
    for pred in notdomain:
        assert not dp.is_domain(pred)
