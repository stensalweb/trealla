:-use_module(library(auth)).

test1 :-
	auth:adduser(user1a,pass1),
	auth:adduser(user1b,pass2),
	true.
test1 :-
	writeln('OOPS already exists').

test2 :-
	auth:adduser(user2a,pass1),
	auth:adduser(user2b,pass2),
	true.
test2 :-
	writeln('OOPS already exists').

test3 :-
	auth:dumpusers.
