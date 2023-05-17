import pytest
from clingo.ast import ASTType, Sign, Transformer, parse_string

from dependency import DomainPredicates  # collect_bound_variables,
from dependency import (PositivePredicateDependency, body_predicates,
                        head_predicates)


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
            [("d", 1)],
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
        assert dp.is_static(pred)
    for pred in notdomain:
        assert not dp.is_static(pred)
    for pred in hasdomain:
        assert dp.has_domain(pred)


@pytest.mark.parametrize(
    "prg, domain_condition",
    [
        (
            """
            a(X) :- b(X,Y), c(Y).
            {d(X)} :- b(X,Y), c(Y).
            e(X) :- a(X).
            {f(X)} :- d(X), a(X).
            {g(X)} :- d(X), a(Y), X <= Y.
            """,
            {
                ("a", 1) : {frozenset([("a", 1)])},
                ("d", 1) : {frozenset(["b(X,Y)", "c(Y)"])},
                ("e", 1) : {frozenset([("e", 1)])},
                ("f", 1) : {frozenset(["__dom_d(X)", "a(X)"])},
                ("g", 1) : {frozenset(["__dom_d(X)", "a(Y)", "X <= Y"])},
            },
        ),
    ],
)
def test_domain_predicates_condition_as_string(prg, domain_condition):
    ast = []
    parse_string(prg, lambda stm: ast.append((stm)))
    dp = DomainPredicates(ast)
    for pred, domain in domain_condition.items():
        assert dp._domain_condition_as_string(pred) == domain


@pytest.mark.parametrize(
    "prg, predicates, domain_program",
    [
        (
            """
            a(X) :- b(X,Y), c(Y).
            {d(X)} :- b(X,Y), c(Y).
            e(X) :- a(X).
            {f(X)} :- d(X), a(X).
            {g(X)} :- d(X), a(Y), X <= Y.
            h(a(X), X+1, 42) :- g(X), not f(X).
            i(4).
            {i(X)} :- a(X).
            {j(X)} :- a(X).
            {j(Y) : b(X,Y)}.
            {k(Y)} :- Y=X+1, a(X).
            {l(Y)} :- Y=X+1, l(X), Y < 100.
            """,
            [("d", 1), ("f", 1), ("g", 1), ("h", 3), ("i", 1), ("j", 1), ("k", 1), ("l", 1)],
            [
                "__dom_d(X) :- b(X,Y); c(Y).",
                "__dom_f(X) :- __dom_d(X); a(X).",
                "__dom_g(X) :- __dom_d(X); a(Y); X <= Y.",
                "__dom_h(a(X),(X+1),42) :- __dom_g(X); not __dom_f(X).",
                "__dom_i(4).",
                "__dom_i(X) :- a(X).",
                "__dom_j(X) :- a(X).",
                "__dom_j(Y) :- b(X,Y).",
                "__dom_k(Y) :- Y = (X+1); a(X).",
            ]
        ),
        (
            """
            {b(Y) : a(Y)}.
            {c(X)} :- X = #sum {1, Y: b(Y)}.
            """,
            [("a", 1), ("b", 1), ("c", 1),],
            [
                "__dom_b(Y) :- a(Y).",
            ]
        ),
        (
            """
            {l(Y)} :- Y=X+1, l(X), Y < 100.
            a(X) :- l(X).
            """,
            [("l", 1), ("a", 1), ("c", 1),],
            []
        ),
        (
            """
            {person(a);
            person(b)}.
            {
            skill(a, ("some",1), 3);
            skill(a, ("thing",1), 5);
            skill(a, ("programming",1..10), 10);
            skill(a, ("knitting",1..10), 100);
            skill(b, t("cooking",1..10), 10);
            skill(b, t("knitting",1..10), 1)}.
            max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).
            """,
            [("max", 2),],
            []
        ),
        (
            """
            {person(a);
            person(b)}.
            max(P, X) :- X = #max {V, ID : skull(P, ID, V)}, person(P).
            """,
            [("max", 2),],
            [
                "__dom_person(a).",
                "__dom_person(b).",
                "__dom_max(P,X) :- X = #max { V,ID: skull(P,ID,V) }; __dom_person(P).",
            ]
        ),

        
    ],
)
def test_domain_predicates_condition(prg, predicates, domain_program):
    ast = []
    parse_string(prg, lambda stm: ast.append((stm)))
    dp = DomainPredicates(ast)
    strlist = []
    for pred in predicates:
        if dp.has_domain(pred):
            strlist.extend(map(str, dp.create_domain(pred)))
    assert sorted(strlist) == sorted(domain_program)
