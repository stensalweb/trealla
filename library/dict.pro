:- module(dict, [get/4, get/3, set/4, del/3]).

get([],_,D,D) :- !.
get([N:V|_],N,V,_) :- !.
get([_|T],N,V,D) :- get(T,N,V,D).

get([],_,_) :- !, fail.
get([N:V|_],N,V) :- !.
get([_|T],N,V) :- get(T,N,V).

set(L,N,V,[N:V|L2]) :- del(L,N,L2).

del([],_,[]) :- !.
del([N:_|T],N,T) :- !.
del([H|T],N,[H|L]) :- del(T,N,L).
