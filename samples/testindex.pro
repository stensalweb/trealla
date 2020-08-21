:- dynamic(f/1).
:- dynamic(g/2).

test1a :-
	write('Load...'), nl,
	between(1,1000000,I),
		assertz(g(I,I)),
		fail.
test1a :-
	write('Search using 1st-arg...'), nl,
	between(1,1000000,I),
		g(I,_),
		fail.
test1a :-
	write('Done... '), write(1000000), write(' items'), nl, true.

test1b :-
	write('Load...'), nl,
	between(1,1000000,I),
		assertz(g(I,I)),
		fail.
test1b :-
	write('Search using 2nd-arg...'), nl,
	between(1,1000000,I),
		g(_,I),
		fail.
test1b :-
	write('Done... '), write(1000000), write(' items'), nl, true.

test2a :-
	write('Load...'), nl,
	between(1,1000000,I),
		assertz(f(I)),
		fail.
test2a :-
	write('Iterate over set...'), nl,
	f(_),
		fail.
test2a :-
	write('Done... '), write(1000000), write(' items'), nl, true.

test2b :-
	write('Load...'), nl,
	between(1,1000000,I),
		assertz(f(I)),
		fail.
test2b :-
	write('Use findall...'), nl,
	findall(N,f(N),L),
	length(L,Count),
	write('Done... '), write(Count), write(' items'), nl,
	true.

test3 :-
	write('Load...'), nl,
	between(1,1000000,I),
		assertz(g(I,I)),
		fail.
test3 :-
	write('Iterate over 2nd-arg...'), nl,
	g(_,_),
		fail.
test3 :-
	write('Done... '), write(1000000), write(' items'), nl,
	true.

test4 :-
	write('Load...'), nl,
	between(1,1000000,I),
		assertz(f(I)),
		fail.
test4 :-
	write('Retract...'), nl,
	retract(f(_)),
		fail.
test4 :-
	write('Done... '), write(1000000), write(' items'), nl, true.

test5 :-
	write('Load...'), nl,
	between(1,10,_),
		between(1,1000000,J),
			assertz(f(J)),
			fail.
test5 :-
	write('Search using once 1st-arg...'), nl,
	between(1,1000000,I),
		once(f(I)),
		%write(I), nl,
		fail.
test5 :-
	write('Done... '), write(1000000), write(' items'), nl, true.

test6 :-
	assertz(ff(3)),
	assertz(ff(2)),
	assertz(ff(1)),
	ff(X),
	write(X), nl,
	fail.
test6.
