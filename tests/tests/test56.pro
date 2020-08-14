% A grammar in DCG

:-initialization(main).

%%%%%%%%%%%%%%%%% Grammar %%%%%%%%%%%%%%%%%%%

sentence --> np, vp.
np --> det, noun.
vp --> verb, np.
vp --> verb.

noun --> [woman].
noun --> [man].
verb --> [shoots].
det --> [the].
det --> [a].

/*
    Generate all possible sentences...
*/

main :- phrase(sentence,X), write(X), nl, fail.
main :- halt.
