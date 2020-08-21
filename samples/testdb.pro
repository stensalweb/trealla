:-use_module(library(auth)).

test1a :-
	auth:adduser(user1,pass1),
	true.
test1a :-
	writeln('OOPS already exists').

test1b :-
	auth:deluser(user1),
	true.
test1b :-
	writeln('OOPS not exists').

test2a :-
	auth:adduser(user2,pass1),
	true.
test2a :-
	writeln('OOPS already exists').

test2b :-
	auth:deluser(user2),
	true.
test2b :-
	writeln('OOPS not exists').

test99 :-
	auth:save,
	auth:listusers(L),
	writeln(L),
	%maplist(writeln,L),
	true.
