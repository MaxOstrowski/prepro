%{a;b;c;d;e;f;g}.
%:- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2, 5>3, X=Y, 1<=X!=4<5.
%:- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.
%:- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, not X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.
%:- not X = #sum{1,a : a;1,b: b;1,c: c; 1,e: e;1,f: f;1,g: g}, not 3 <= X <= 4.

%#false :- 1 { a : e; b : not f; c } 2, d.
%#false :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2, 5>3, X=Y, 1<=X!=4<5.
%#sum{1:a;1:b}.
%{a : b; c}.
%a : b;c.
%#false :- 1 { a; b; c } 2, d.
%x;y.


%b :- a.
%c :- b.
%d :- c.
%a :- d.
%e :- d.


%e :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2.

{person(a);
person(b)}.
{
skill(a, ("some",1), 3);
skill(a, ("thing",1), 5);
skill(a, ("programming",1..10), 10);
skill(a, ("knitting",1..10), 100);
skill(b, t("cooking",1..10), 10);
skill(b, t("knitting",1..10), 1)}.
%max(P, X) :- X = #max {V, ID : skill(P, ID, V)}, person(P).
% - I need the domain of V
% - V needs to be static domain
% - what if V is a formula with more than one variable ? This applies to all of them
% But it is actually the formula that we have to create a domain for
% I need to get a list of all expressions in the body that do have a GLOBAL Variable that also occurs in the aggregate,
% these elements also need to be positive in the body, not negatively.


% __dom_skill_3_3(1).
% __dom_skill_3_3(3).
% __dom_skill_3_3(5).
% __dom_skill_3_3(10).
% __dom_skill_3_3(100).
% __min_dom_skill_3_3(X) :- X = #min{L : __dom_skill_3_3(L)}.
% __next_dom_skill_3_3(P,N) :- __min_dom_skill_3_3(P), __dom_skill_3_3(N), N > P,
% not __dom_skill_3_3(B) : __dom_skill_3_3(B), P < B < N.
% __next_dom_skill_3_3(P,N) :- __next_dom_skill_3_3(_,P), __dom_skill_3_3(N), N > P,
% not __dom_skill_3_3(B) : __dom_skill_3_3(B), P < B < N.

% __chain(E, V) :- skill(E, ID, V), person(E).
% __chain(E, P) :- __chain(E, N), __next_dom_skill_3_3(P, N).
% max(E, V) :- __chain(E, V), not __chain(E, N) : __next_dom_skill_3_3(V, N).
% max(E, #inf) :- __min_dom_skill_3_3(X), not __chain(E, X), person(E).
