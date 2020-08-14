:- module(lists,
	[member/2, memberchk/2, select/3, selectchk/3, subtract/3, union/3,
	intersection/3, reverse/2, append/3, nth/3, nth1/3, nth0/3]).

member(X,[X|_]).
member(X,[_|T]) :- member(X,T).

memberchk(T,L) :- member(T,L), !.

select(X,[X|T],T).
select(X,[H|T],[H|Rest]) :- select(X,T,Rest).

selectchk(X,L,Rest) :- select(X,L,Rest), !.

subtract([],_,[]) :- !.
subtract([H|T],L2,L3) :- memberchk(H,L2),!, subtract(T,L2,L3).
subtract([H|T1],L2,[H|T3]) :- subtract(T1,L2,T3).

union([],L,L).
union([H|T],Y,Z):- member(H,Y), !, union(T,Y,Z).
union([H|T],Y,[H|Z]):- union(T,Y,Z).

intersection([],_,[]).
intersection([H|T],Y,[H|Z]) :- member(H,Y), !, intersection(T,Y,Z).
intersection([_|T],Y,Z) :- intersection(T,Y,Z).

revzap([],L,L) :- !.
revzap([H|L],L2,L3) :- revzap(L,[H|L2],L3).
reverse(L1,L2) :- revzap(L1,[],L2).

append([],L,L).
append([H|T],L,[H|R]) :- append(T,L,R).

nth(1,[H|_],H).
nth(N,[_|T],H) :- nth(M,T,H), N is M + 1.

nth1(1,[H|_],H).
nth1(N,[_|T],H) :- nth1(M,T,H), N is M + 1.

nth0(0,[H|_],H).
nth0(N,[_|T],H) :- nth0(M,T,H), N is M + 1.
