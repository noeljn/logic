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

%premise
verifyLine([LineNum, Term, premise], Prems, _) :- member(Term, Prems), lineVerifyPrint(LineNum).

verifyLine([LineNum, _, assumption], Prems, _) :- lineVerifyPrint(LineNum).

%assumption
verifyLine([[LineNum, Term, assumption]|T], Prems, Proof) :- verifyProof([[LineNum, Term, assumption]|T], Prems, Proof), lineVerifyPrint(LineNum).

%copy
verifyLine([LineNum, Term, copy(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, Term), compareLevel(LineNum, Proof, copy(X)), lineVerifyPrint(LineNum).

%andint
verifyLine([LineNum, Term, andint(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, TermY), Term == and(TermX, TermY), compareLevel(LineNum, Proof, andint(X,Y)), lineVerifyPrint(LineNum).

%andel
verifyLine([LineNum, Term, andel1(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, and(Term,_)), compareLevel(LineNum, Proof, andel1(X)), lineVerifyPrint(LineNum).
verifyLine([LineNum, Term, andel2(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, and(_,Term)), compareLevel(LineNum, Proof, andel2(X)), lineVerifyPrint(LineNum).

%orint
verifyLine([LineNum, Term, orint1(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, or(Term,_)), compareLevel(LineNum, Proof, orint1(X)), lineVerifyPrint(LineNum).
verifyLine([LineNum, Term, orint2(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, or(_,Term)), compareLevel(LineNum, Proof, orint2(X)), lineVerifyPrint(LineNum).

%orel
verifyLine([LineNum, Term, orel(X,Y,U,V,W)], _, Proof) :- X < LineNum, 
findTerm(X, Proof, or(TermX, TermY)), 
findTerm(Y, Proof, TermX),
findTerm(U, Proof, Term), 
findTerm(V, Proof, TermY), 
findTerm(W, Proof, Term), lineVerifyPrint(LineNum).  

verifyLine([LineNum, imp(TermX,TermY), impint(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, TermY), compareLevel(LineNum, Proof, impint(X,Y)), lineVerifyPrint(LineNum).

verifyLine([LineNum, Term, impel(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(Y, Proof, imp(TermX, Term)), findTerm(X, Proof, TermX), compareLevel(LineNum, Proof, impel(X,Y)), lineVerifyPrint(LineNum).

getFirstOfList([H|T], H).
getSecondOfList([_,B|T], B).
%getThirdOfList([_,_,C|T], C).

%Tries to find the term in the proof at a line
findTerm(LineNum,[], Term) :- false.
findTerm(LineNum, [Line|T], Term) :- getFirstOfList(Line, LineNum), getSecondOfList(Line, Term).
findTerm(LineNum, [[Line|Ts]|T], Term) :- getFirstOfList(Line, LineNum), getSecondOfList(Line, Term).
findTerm(LineNum, [[Line|Ts]|T], Term) :- findTerm(LineNum, Ts, Term).
findTerm(LineNum, [Line|T], Term) :- findTerm(LineNum, T, Term).

lineVerifyPrint(LineNum) :- write("Line "),write(LineNum),write(" fullfilled"),write("\n").
levelPrint(LineNum) :- write("Level "),write(LineNum),write("\n").

boxLevel(LineNum,[], BoxLevel, ResBoxLevel) :- false.
boxLevel(LineNum, [Line|T], BoxLevel, ResBoxLevel) :- getFirstOfList(Line, LineNum), ResBoxLevel = BoxLevel.
boxLevel(LineNum, [Line|T], BoxLevel, ResBoxLevel) :- getFirstOfList(Line, H), isList(H), NewLevel is BoxLevel + 1, boxLevel(LineNum, Line, NewLevel, ResBoxLevel).
boxLevel(LineNum, [Line|T], BoxLevel, ResBoxLevel) :- boxLevel(LineNum, T, BoxLevel, ResBoxLevel).

%Checks if argument is list 
isList([_|_]).
isList([]).

compareLevel(LineNum, Proof, Func) :- arg(1, Func, Value), boxLevel(LineNum, Proof, 0, Level), boxLevel(Value, Proof, 0, ValueLevel), Level >= ValueLevel.
compareLevel(LineNum, Proof, Func) :- arg(1, Func, Value), arg(2, Func, SecValue), 
boxLevel(LineNum, Proof, 0, Level), boxLevel(Value, Proof, 0, ValueLevel), boxLevel(SecValue, Proof, 0, SecValueLevel), 
Level >= ValueLevel, Level >= SecValueLevel.

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