:- initialization(main).

main :-
	read_term_from_atom('[1,2,3]', Term, []),
	write(Term), nl, halt.
