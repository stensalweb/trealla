:- initialization(main).

main :- (true -> write(foo1) ; write(bar1)), nl, fail.
main :- (false -> write(foo2) ; write(bar2)), nl, fail.
main :- halt.
