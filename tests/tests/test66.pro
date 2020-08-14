main :-
	X1 is pi, write(X1), nl,
	X2 is e, write(X2), nl,
	X3 is 1 / 10, write(X3), nl,
	Y4 is 1 / 7, X4 is rationalize(Y4), write(X4), nl,
	halt.

:- initialization(main).
