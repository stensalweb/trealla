test1 :-
	\+ \+ true,
	writeln(ok).
test1 :-
	writeln(failed).

task2 :- writeln('OK about to throw'), throw(error(p1,p2)).

test2 :-
	( catch(task2,E,(format('OK caught: ~w~n', [E]),fail)) ->
		writeln('OOPS no error') ; writeln('OK was error')
	),
	writeln('OK done').

task3 :- writeln('OK here').

test3 :-
	( catch(task3,E,(format('wrong, caught: ~w~n', [E]),fail)) ->
		writeln('OK no error') ; writeln('OOPS was error')
	),
	writeln('OK done').

test4a :-
	( call(writeln('OK here')) ->
		writeln('OK no error') ; writeln('OOPS was error')
	),
	writeln('OK done (3rd line)').

test4b :-
	( call(writeln, 'OK here') ->
		writeln('OK no error') ; writeln('OOPS was error')
	),
	writeln('OK done (3rd line)').

test4c :-
	( call(writeln, 'OK here') -> writeln('OK no error') ),
	writeln('OK done (3rd line)').

test5a :- throw(error(p1,p2)).
test5b :- _ is abs(abc).

test6 :- Orig='Aa...Bb...Cc...Dd',sys_queue(Orig),string_lower(Orig,S),sys_queue(S),fail.
test6 :- sys_list(L),writeln(L).

test7 :-
	http_get('www.duckduckgo.com',Data,[status_code(Code),headers(Hdrs)]),
	write('Response='), writeln(Code),
	writeln(Hdrs),
	write(Data), nl.

test8 :-
	http_get('http://www.bing.com',Data,[status_code(Code),headers(Hdrs)]),
	write('Response='), writeln(Code),
	writeln(Hdrs),
	write(Data), nl.

test9 :-
	http_get('https://www.google.com',Data,[status_code(Code),headers(Hdrs)]),
	write('Response='), writeln(Code),
	writeln(Hdrs),
	write(Data), nl.

task10(C) :-
	repeat,
		(at_end_of_stream(C) -> (!, fail) ; true),
		getline(C,L),
		write('GOT: '), writeln(L),
		fail.
task10(_).

test10a :-
	fork,
	server(':8080',S,[]),
	accept(S,C),
		fork,
		task10(C).
test10a :-
	wait.

test10b :-
	client('localhost:8080',_,_,S,[]),
	between(1,1000000,I),
		format(S,'[~d] Hello, world~n',[I]),
		delay(100),
		fail.

task11(C) :-
	repeat,
		getline(C,L),
		write('GOT: '), writeln(L),
		fail.
task11(_).

test11a :-
	fork,
	server(':8080',S,[udp(true)]),
	task11(S).
test11a :-
	wait.

test11b :-
	client('localhost:8080',_,_,S,[udp(true)]),
	between(1,1000000,I),
		format(S,'[~d] Hello, world~n',[I]),
		delay(100),
		fail.

test12 :-
	JsonData = '[{"foo":1,"bar":2}, {"bar":3,"foo":4}]',
	read_term_from_atom(JsonData, Data, [double_quotes(atom)]),
	findall(X, (member({F1:A,F2:B},Data), (F1=foo -> X = A ; (F2=foo -> X = B))), L),
	writeln(L).

test13.
test13 :- test13.

sum14(I,I,T,T) :- !.
sum14(I,X,Tmp,T) :- NewTmp is Tmp+I, NewI is I+1, sum14(NewI,X,NewTmp,T).

test14 :-
	sum14(1,100000,0,T),
	write(T), nl.

integers(Low,High,[Low|Rest]) :-
	Low =< High,
	!,
	M is Low+1,
	integers(M,High,Rest).
integers(_,_,[]).

test15a :- integers(1, 100000, L), L=[H|_], write(H), nl.
test15b:- integers(1, 100000, L), L=[_|T], write(T), nl.
test15c:- integers(1, 1000000, L), write_term(L,[max_depth(0)]), nl.

:- dynamic(p/2).
:- dynamic(p/3).

test16 :-
	assertz(p(Z, h(Z, W), f(W))), write('ok14\n'),
	p(f(f(a)), h(f(f(a)), f(a)), f(f(a))), write('ok15\n').
test16 :- write(failed), nl.

f(a,1).
f(a,2).
f(a,3).
f(b,10).
f(b,20).
f(b,30).

test17 :-
	findall(X,f(a,X),Bag,Tail),
	write(Bag), nl,
	findall(X,f(b,X),Tail,_NewTail),
	write(Bag), nl.

test18a :- assertz(f18(123),R), assertz(f18(456)), erase(R), listing(f18).
test18b :- assertz(f18(123),_), clause(f18(X),B,_).

task50(T) :-
	between(1,inf,_),
		format('Task ... ~d',[T]), nl,
		sleep(T),
		fail.

test50 :- between(1,4,I), fork, task50(I).
test50 :- wait.

task51(T) :- Ms is random(1000), delay(Ms), send(T).

test51 :- between(1,10,I), fork, task51(I).
test51 :- wait, sys_list(L), writeln(L).

test52 :- between(1,10,_), N is random(1000), sys_queue(N), fail.
test52 :- sys_list(L), sort(L,L2),
	write_term_to_atom(S,L2,[]), writeln(S), nl,
	read_term_from_atom(S,S2,[]), write_term(S2,[]), nl.

task53(T) :- between(1,10,_), R is random(1000), delay(R), send({T,R}), fail.
task53(T) :- format('Task ~d done~n',[T]).

test53 :- between(1,4,I), fork, task53(I).
test53 :-
	forall(await, (recv(Msg), format('Got: ~w~n',[Msg]))),
	format('Finished~n').

geturl(Url) :-
	http_get(Url,_Data,[status_code(Code),final_url(Location)]), !,
	format('Job [~w] ~w ==> ~w done~n',[Url,Code,Location]).

test54 :-
	L = ['www.google.com','www.bing.com','www.duckduckgo.com'],
	maplist(geturl,L),
	writeln('Finished').

test55 :-
	L = ['www.google.com','www.bing.com','www.duckduckgo.com'],
	maplist(spawn(geturl),L),
	wait, writeln('Finished').

task56(Url) :-
	http_open([host(Url),path('/'),method('head')],S,[status_code(Code)]),
	close(S),
	writeln(Code).

test56 :-
	L = ['www.google.com','www.bing.com','www.duckduckgo.com'],
	maplist(task56,L),
	writeln('Finished').
