verify(InputFileName) :- see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    valid_proof(Prems, Goal, Proof).


valid_proof(Prems, Goal, Proof) :- verifyLastLine(Goal, Proof), verifyProof(Proof, Prems, Proof).

verifyLastLine(Goal, Proof) :- 
/*
verifyLastLine

verifyLine

verifyProof
copY(X)

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