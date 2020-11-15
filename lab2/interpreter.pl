verify(InputFileName) :- see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).


valid_proof(Prems, Goal, Proof) :- verifyLastLine(Goal, Proof), verifyProof(Proof, Prems, Proof).

%
verifyLastLine(Goal, Proof) :- last(Proof,LastLine), checkLastLine(LastLine, Goal).

%Checks if the term of the last line is equal to the Goal
checkLastLine([_, Term, _], Goal) :- Term == Goal.

%
verifyProof([], _, _).
verifyProof([H|T], Prems, Proof) :- verifyLine(H, Prems, Proof), verifyProof(T, Prems, Proof). 

verifyLine([_, Term, premise], Prems, _) :- member(Term, Prems).

verifyLine([LineNum, Term, copy(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, Term).

verifyLine([LineNum, Term, andint(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, TermY), Term == and(TermX, TermY).

getFirstOfList([H|T], H).
getSecondOfList([_,B|T], B).
getThirdOfList([_,_,C|T], C).

findTerm(LineNum,[], Term) :- false.
findTerm(LineNum, [H|T], Term) :- getFirstOfList(H, LineNum), getSecondOfList(H, Term).
findTerm(LineNum, [H|T], Term) :- findTerm(LineNum, T, Term).


premise(X,Y) :- false.
%verifyLine([[LineNum, Term, assumption]|T], Prems, Proof) :-




/*


% En lista av premisser (v¨anstra delen av sekventen.)
[neg(neg(imp(p, neg(p))))].

% M˚alet (h¨ogra delen av sekventen).
neg(p).

% Beviset

[
    [1, neg(neg(imp(p,neg(p)))), premise ],
    [2, imp(p, neg(p)), negnegel(1)],
    [
        [3, p, assumption ],
        [4, neg(p), impel(3,2) ],
        [5, cont, negel(3,4) ]
    ],
    [6, neg(p), negint(3,5)]
].

copy(X)

premise(X,Y)

assumption(X,Y)

andint(X,Y)
andel1(X)
andel2(X)

orint1(X)
orint2(X)

orel(X,Y,U,V,W)

impint(X,Y)

impel(X,Y)

negint(X,Y)

negel(X,Y)

contel(X)

negnegint(X)
negnegel(X)

mt(X,Y)

pbc(X,Y)

lem(X)

*/