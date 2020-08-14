main :-
	( call(writeln, 'OK here') ->
		writeln('OK no error') ; writeln('OOPS was error')
	),
	writeln('OK done (3rd line)'),
	halt.

:- initialization(main).
