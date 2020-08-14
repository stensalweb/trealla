:-initialization(main).

f6(X,Y) :- arg(X,f(a,b,c,d,e,f),Y), write(X), write(' <==> '), write(Y), nl, fail.
f6(_X,_Y).

main :- f6(X,Y), var(X), var(Y), halt.
