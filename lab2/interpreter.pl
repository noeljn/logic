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

%assumption
verifyLine([[LineNum, Term, assumption]|T], Prems, Proof) :- verifyProof(T, Prems, Proof), lineVerifyPrint(LineNum).

%copy
verifyLine([LineNum, Term, copy(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, Term), compareLevel(LineNum, Proof, copy(X)), compareBoxNumber(LineNum, Proof, copy(X)), ! , lineVerifyPrint(LineNum).

%andint
verifyLine([LineNum, Term, andint(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, TermY), Term == and(TermX, TermY), compareBoxNumber(LineNum, Proof, andint(X,Y)), lineVerifyPrint(LineNum).

%andel
verifyLine([LineNum, Term, andel1(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, and(Term,_)), compareLevel(LineNum, Proof, andel1(X)), compareBoxNumber(LineNum, Proof, andel1(X)), lineVerifyPrint(LineNum).
verifyLine([LineNum, Term, andel2(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, and(_,Term)), compareLevel(LineNum, Proof, andel2(X)), compareBoxNumber(LineNum, Proof, andel2(X)), lineVerifyPrint(LineNum).

%orint
verifyLine([LineNum, Term, orint1(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, or(Term,_)), compareLevel(LineNum, Proof, orint1(X)), compareBoxNumber(LineNum, Proof, orint1(X)), lineVerifyPrint(LineNum).
verifyLine([LineNum, Term, orint2(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, or(_,Term)), compareLevel(LineNum, Proof, orint2(X)), compareBoxNumber(LineNum, Proof, orint2(X)), lineVerifyPrint(LineNum).

%orel
verifyLine([LineNum, Term, orel(X,Y,U,V,W)], _, Proof) :- X < LineNum, 
findTerm(X, Proof, or(TermX, TermY)), 
findTerm(Y, Proof, TermX),
findTerm(U, Proof, Term), 
findTerm(V, Proof, TermY), 
findTerm(W, Proof, Term),
compareLevel(LineNum, Proof, orel(X,Y,U,V,W)), compareBoxNumber(LineNum, Proof, orel(X,Y,U,V,W)),
!,lineVerifyPrint(LineNum).  

verifyLine([LineNum, imp(TermX,TermY), impint(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, TermY), compareLevel(LineNum, Proof, impint(X,Y)), compareBoxNumber(LineNum, Proof, impint(X,Y)), ! , lineVerifyPrint(LineNum).

verifyLine([LineNum, Term, impel(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(Y, Proof, imp(TermX, Term)), findTerm(X, Proof, TermX), compareLevel(LineNum, Proof, impel(X,Y)), compareBoxNumber(LineNum, Proof, impel(X,Y)), lineVerifyPrint(LineNum).

verifyLine([LineNum, Term, negint(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, cont), neg(TermX) == Term, compareLevel(LineNum, Proof, negint(X,Y)), lineVerifyPrint(LineNum).
verifyLine([LineNum, Term, negel(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, TermX), findTerm(Y, Proof, TermY), neg(TermX) == TermY, compareLevel(LineNum, Proof, negel(X,Y)), Term == cont, ! , lineVerifyPrint(LineNum) .

%contel
verifyLine([LineNum, _, contel(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, cont), compareLevel(LineNum, Proof, contel(X)), compareBoxNumber(LineNum, Proof, contel(X)), lineVerifyPrint(LineNum).

%negnegint
%negnegel
verifyLine([LineNum, Term, negnegint(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, TermX), arg(1, Term, InTerm), arg(1, InTerm, TermX), compareLevel(LineNum, Proof, negnegint(X,Y)), compareBoxNumber(LineNum, Proof, negnegint(X)), lineVerifyPrint(LineNum). 
verifyLine([LineNum, Term, negnegel(X)], _, Proof) :- X < LineNum, findTerm(X, Proof, neg(neg(Term))), compareLevel(LineNum, Proof, negnegel(X,Y)), compareBoxNumber(LineNum, Proof, negnegel(X)), lineVerifyPrint(LineNum).

%mt(X,Y)
verifyLine([LineNum, Term, mt(X,Y)], _, Proof) :- X < LineNum , Y < LineNum, arg(1, Term, InTerm), findTerm(X, Proof, TermX), arg(1, TermX, InTerm), arg(2, TermX, InTermX ), findTerm(Y, Proof, neg(InTermX)), compareLevel(LineNum, Proof, mt(X,Y)), compareBoxNumber(LineNum, Proof, impel(X,Y)), lineVerifyPrint(LineNum).

%pbc(X,Y)
verifyLine([LineNum, Term, pbc(X,Y)], _, Proof) :- X < LineNum, Y < LineNum, findTerm(X, Proof, neg(Term)), findTerm(Y, Proof, cont), compareLevel(LineNum, Proof, pbc(X,Y)), lineVerifyPrint(LineNum).

%lem
verifyLine([LineNum, or(neg(P), P), lem], _, Proof) :- lineVerifyPrint(LineNum).
verifyLine([LineNum, or(P, neg(P)), lem], _, Proof) :- lineVerifyPrint(LineNum).

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
%testPrint(LineNum) :- write("Box number "),write(LineNum),write("\n").


%Finds the level of a line
boxLevel(LineNum,[], BoxLevel, ResBoxLevel) :- false.
boxLevel(LineNum, [Line|T], BoxLevel, ResBoxLevel) :- getFirstOfList(Line, LineNum), ResBoxLevel = BoxLevel.
boxLevel(LineNum, [Line|T], BoxLevel, ResBoxLevel) :- getFirstOfList(Line, H), isList(H), NewLevel is BoxLevel + 1, boxLevel(LineNum, Line, NewLevel, ResBoxLevel).
boxLevel(LineNum, [Line|T], BoxLevel, ResBoxLevel) :- boxLevel(LineNum, T, BoxLevel, ResBoxLevel).

%Counts how many boxes you have and the starting line for each box
countBoxes([], Count, ResCount, StartNum, ResStartNum) :- ResCount = Count, ResStartNum = StartNum.
countBoxes([Line|T], Count, ResCount, StartNum, [LineNum|ResStartNum]) :- getFirstOfList(Line, H), isList(H), getFirstOfList(H, LineNum), NewCount is Count + 1, countBoxes(T, NewCount, ResCount, StartNum , ResStartNum).
countBoxes([Line|T], Count, ResCount, StartNum, ResStartNum) :- countBoxes(T, Count, ResCount, StartNum, ResStartNum).


%Gets the box number of a line with line number 'LineNum'. If Its not in a box, the LineNum will be equal to 0.
detBox(LineNum, Proof, ResBoxNum) :- boxLevel(LineNum, Proof, 0, Level), Level = 0, ResBoxNum = 0.
detBox(LineNum, Proof, ResBoxNum) :- countBoxes(Proof, 0, Boxes, [] , StartNum),elementComp(StartNum, LineNum, 0, ResPos), ResBoxNum = ResPos, boxLevel(LineNum, Proof, 0, Level), Level > 0.

elementComp([], Element, Pos, ResPos) :- ResPos is 0.
elementComp([H|[]], Element, Pos, ResPos) :- ResPos is Pos + 1.
elementComp([H|T], Element, Pos, ResPos) :- Element >= H, getFirstOfList(T, Ht), Element < Ht, ResPos is Pos + 1.
elementComp([H|T], Element, Pos, ResPos) :- NewPos is Pos + 1, elementComp(T, Element, NewPos, ResPos).

%Checks if argument is list 
isList([_|_]).
isList([]).

%Makes sure that all Func point to the same box or one of the two values points to something outside any box.
compareBoxNumber(LineNum, Proof, Func) :- arg(1, Func, Value), not(arg(2, Func, _)), detBox(Value, Proof, ResValue), detBox(LineNum, Proof, ResLineNum), ResValue = 0.
compareBoxNumber(LineNum, Proof, Func) :- arg(1, Func, Value), not(arg(2, Func, _)), detBox(Value, Proof, ResValue), detBox(LineNum, Proof, ResLineNum), !, ResLineNum = ResValue.
compareBoxNumber(LineNum, Proof, Func) :- arg(1, Func, Value), arg(2, Func, SecValue), detBox(Value, Proof, ResValue), detBox(SecValue, Proof, ResSecValue), !, boxNumberHelper(ResValue, ResSecValue).
compareBoxNumber(LineNum, Proof, Func) :- arg(1, Func, Value), arg(2, Func, Value2), arg(3, Func, Value3), arg(4, Func, Value4), arg(5, Func, Value5), 
detBox(Value, Proof, ResValue), detBox(Value2, Proof, ResValue2), detBox(Value3, Proof, ResValue3), detBox(Value4, Proof, ResValue4), detBox(Value5, Proof, ResValue5), detBox(LineNum, Proof, ResLineNum),
boxNumberHelper(ResValue, ResValue2, ResValue3, ResValue4, ResValue5, ResLineNum).

boxNumberHelper(ResValue, ResValue2, ResValue3, ResValue4, ResValue5, ResLineNum) :- ResValue2 = ResValue3, ResValue4 = ResValue5, ResLineNum = ResValue.
boxNumberHelper(0, ResValue2, ResValue3, ResValue4, ResValue5, ResLineNum) :- ResValue2 = ResValue3, ResValue4 = ResValue5.
boxNumberHelper(ResValue, 0) :- true.
boxNumberHelper(ResValue, ResSecValue) :- ResValue = ResSecValue.
boxNumberHelper(0, ResSecValue) :- true.

%Comapres the level of different lines. This makes sure that the targets of the Func are at most within 1 level of eachother. And for those that should be on the same level, it checks for that too.
compareLevel(LineNum, Proof, Func) :- arg(1, Func, Value), boxLevel(LineNum, Proof, 0, Level), boxLevel(Value, Proof, 0, ValueLevel), Level >= ValueLevel.
compareLevel(LineNum, Proof, Func) :- arg(1, Func, Value), arg(2, Func, SecValue), 
boxLevel(LineNum, Proof, 0, Level), boxLevel(Value, Proof, 0, ValueLevel), boxLevel(SecValue, Proof, 0, SecValueLevel), Diff is ValueLevel-Level, Diff2 is SecValueLevel-Level,
Diff < 2, Diff2 < 2, ValueLevel == SecValueLevel.
compareLevel(LineNum, Proof, Func) :- arg(1, Func, Value), arg(2, Func, Value2), arg(3, Func, Value3), arg(4, Func, Value4), arg(5, Func, Value5),
boxLevel(LineNum, Proof, 0, Level), boxLevel(Value, Proof, 0, ValueLevel), boxLevel(Value2, Proof, 0, ValueLevel2), boxLevel(Value3, Proof, 0, ValueLevel3),
boxLevel(Value4, Proof, 0, ValueLevel4), boxLevel(Value5, Proof, 0, ValueLevel5),
ValueLevel2 = ValueLevel3, ValueLevel4 = ValueLevel5,
Diff is ValueLevel-Level, Diff < 2.
