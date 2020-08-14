:- initialization(main).

foo([bar(a), bar(b), bar(c), bar(d)]).

main :- foo(Bars), member(bar(Bar), Bars), write(Bar), nl, fail.
main :- halt.
