:-initialization(main).

main :- sub_atom(abc,B,L,A,S),write([B,L,A,S]), nl, fail.
main :- nl, sub_atom(abc,B,2,A,S),write([B,2,A,S]), nl, fail.
main :- nl, sub_atom(abc,0,2,A,S),write([0,2,A,S]), nl, fail.
main :- nl, sub_atom(abc,0,L,A,S),write([0,L,A,S]), nl, fail.
main :- nl, sub_atom(abc,B,L,0,S),write([B,L,0,S]), nl, fail.
main :- nl, sub_atom(abc,B,2,0,S),write([B,2,0,S]), nl, fail.
main :- halt.
