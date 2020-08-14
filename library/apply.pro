:- module(apply, [maplist/2, maplist/3, maplist/4]).

maplist(_,[]).
maplist(P,[X1|X1s]) :- call(P,X1), maplist(P,X1s).

maplist(_,[],[]).
maplist(P,[X1|X1s],[X2|X2s]) :- call(P,X1,X2), maplist(P,X1s,X2s).

maplist(_,[],[],[]).
maplist(P,[X1|X1s],[X2|X2s],[X3|X3s]) :- call(P,X1,X2,X3), maplist(P,X1s,X2s,X3s).

maplist(_,[],[],[],[]).
maplist(P,[X1|X1s],[X2|X2s],[X3|X3s],[X4|X4s]) :- call(P,X1,X2,X3,X4), maplist(P,X1s,X2s,X3s,X4s).
