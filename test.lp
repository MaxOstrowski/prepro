{a;b;c;d;e;f;g}.
:- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2, 5>3, X=Y, 1<=X!=4<5.
:- 1 <= #sum {1,a : a;1,b: b;1,c: c} <= 2, X = #sum {1,e: e;1,f: f;1,g: g} 3, X>=2>1, 5>3.
%:- not X = #sum{1,a : a;1,b: b;1,c: c; 1,e: e;1,f: f;1,g: g}, not 3 <= X <= 4.


