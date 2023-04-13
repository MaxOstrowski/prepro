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


e :- 1 <= #sum { 1,a: a; 1,b: b; 1,c: c } <= 2, X = #sum { 1,e: e; 1,f: f; 1,g: g } 3, X>=2.


