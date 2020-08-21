:-use_module(library(auth)).

test1a :-
	auth:adduser(user1a,pass1),
	auth:adduser(user1b,pass2),
	true.
test1a :-
	writeln('OOPS already exists').

test1b :-
	auth:deluser(user1a),
	auth:deluser(user1b),
	true.
test1b :-
	writeln('OOPS not exists').

test2a :-
	auth:adduser(user2a,pass1),
	auth:adduser(user2b,pass2),
	true.
test2a :-
	writeln('OOPS already exists').

test2b :-
	auth:deluser(user2a),
	auth:adduser(userbb),
	true.
test2b :-
	writeln('OOPS not exists').

test99 :-
	auth:listusers(L),
	writeln(L),
	%maplist(writeln,L),
	true.
