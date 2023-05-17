import pytest
from clingo.ast import ASTType, Sign, Transformer, parse_string

from dependency import DomainPredicates
from minmax_aggregates import MinMaxAggregator

from difflib import ndiff
@pytest.mark.parametrize(
    "prg, converted_prg",
    [
        (
"""
{person(a);person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)
}.
max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).
""",
"""#program base.
{ person(a); person(b) }.
{ skill(a,("some",1),3); skill(a,("thing",1),5); skill(a,("programming",(1..10)),10); skill(a,("knitting",(1..10)),100); skill(b,t("cooking",(1..10)),10); skill(b,t("knitting",(1..10)),1) }.
__dom_skill(a,("some",1),3).
__dom_skill(a,("thing",1),5).
__dom_skill(a,("programming",(1..10)),10).
__dom_skill(a,("knitting",(1..10)),100).
__dom_skill(b,t("cooking",(1..10)),10).
__dom_skill(b,t("knitting",(1..10)),1).
__dom_person(a).
__dom_person(b).
__dom___max_0_0_11(V) :- __dom_skill(P,ID,V); __dom_person(P).
__min_0__dom___max_0_0_11(X) :- X = #min { L: __dom___max_0_0_11(L) }.
__max_0__dom___max_0_0_11(X) :- X = #max { L: __dom___max_0_0_11(L) }.
__next_0__dom___max_0_0_11(P,N) :- __min_0__dom___max_0_0_11(P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__next_0__dom___max_0_0_11(P,N) :- __next_0__dom___max_0_0_11(_,P); __dom___max_0_0_11(N); N > P; not __dom___max_0_0_11(B): __dom___max_0_0_11(B), P < B < N.
__chain_down___max_0_0_11(P,V) :- skill(P,ID,V); person(P).
__chain_down___max_0_0_11(P,__PREV) :- __chain_down___max_0_0_11(P,__NEXT); __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,__PREV) :- __chain_down___max_0_0_11(P,__PREV); not __chain_down___max_0_0_11(P,__NEXT): __next_0__dom___max_0_0_11(__PREV,__NEXT).
__max_0_0_11(P,#inf) :- __min_0__dom___max_0_0_11(__NEXT); not __chain_down___max_0_0_11(P,__NEXT); person(P).
max(P,X) :- __max_0_0_11(P,X).""",
        ),
    ],
)
def test_minmax_aggregates(prg, converted_prg):
    ast = []
    parse_string(prg, lambda stm: ast.append((stm)))
    dp = DomainPredicates(ast)
    mma = MinMaxAggregator(ast, dp)
    output = "\n".join(map(lambda x: str(x), mma.execute(ast)))
    assert converted_prg == output