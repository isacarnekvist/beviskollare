verify(InputFileName)   :-  readProof(InputFileName, Prems, Goal, Proof),
                            checkEndLineNumber(Proof, Last), !,
                            valid_proof(Prems, Goal, Last, Proof, []), !.

% Vanlig rad
checkPremises([[_,_,F]|T], LastWasPremise)              :-(F == premise, LastWasPremise, !, checkPremises(T, true));
                                                            (F \== premise, !, checkPremises(T, false)).
% Box
checkPremises([[[_,_,assumption]|BT]|T], _)             :-	checkPremises(BT, false),
                                                            checkPremises(T, false).
checkPremises([],_).

checkEndLineNumber([_|T], Last)                         :-  checkEndLineNumber(T, Last).
checkEndLineNumber([[Last,_,_]|[]], Last).

% Last line!
valid_proof(Prems, G1, Stop, [[Stop,G2,F]|_], Proved)  :-  !, checkLine(Prems, [Stop,G2,F], Proved),
                                                            G1 == G2.
% Box, add to proven, prove when asked for
valid_proof(Prems, G, Stop, [[[L,D,assumption]|BT]|T], Proved)   :-  valid_proof(Prems, G, Stop, T, [[[L,D]|BT]|Proved]).

% Otherwise, usual line
valid_proof(Prems, G, Stop, [[L,D,R]|T], Proved)        :-  !, checkLine(Prems, [L, D, R], Proved), !, % Regeln behövs inte i Proved
                                                            valid_proof(Prems, G, Stop, T, [[L,D]|Proved]).

% Empty proof
valid_proof(_,_,_,[],_).

checkLine(Prems, [_, D, premise], _)                    :-  member(D, Prems), !.
checkLine(_, [_, B, impel(X,Y)], Proved)                :-  member([Y, imp(A,B)], Proved), member([X, A], Proved), !.
checkLine(_, [_, neg(A), mt(X,Y)], Proved)              :-  member([X, imp(A,B)], Proved), member([Y, neg(B)], Proved), !.
checkLine(_, [_, A, negnegel(X)], Proved)               :-  member([X, neg(neg(A))], Proved), !.
checkLine(Prems, [_, imp(A,B), impint(X,Y)], Proved)    :-  getBox(X,Box,Proved),
                                                            [[X,A]|T] = Box, 
                                                            valid_proof(Prems, B, Y, T, [[X,A]|Proved]).
checkLine(Prems, [_, B, orel(X,F1,T1,F2,T2)], Proved)   :-  getBox(F1,Box1,Proved), 
                                                            [[F1,A1]|BT1] = Box1,
                                                            valid_proof(Prems, B, T1, BT1, [[F1,A1]|Proved]),
                                                            getBox(F2,Box2,Proved), 
                                                            [[F2,A2]|BT2] = Box2, 
                                                            valid_proof(Prems, B, T2, BT2, [[F2,A2]|Proved]),
                                                            (member([X, or(A1, A2)], Proved); member([X, or(A2, A1)], Proved)).
checkLine(_, [_, A, copy(X)], Proved)                   :-  member([X, A], Proved), !.
checkLine(_, [_, and(A,B), andint(X,Y)], Proved)        :-  member([X, A], Proved),
                                                            member([Y, B], Proved).
checkLine(_, [_, A, andel1(X)], Proved)                 :-  member([X, and(A,_)], Proved).
checkLine(_, [_, B, andel2(X)], Proved)                 :-  member([X, and(_,B)], Proved).
checkLine(_, [_, or(A,_), orint1(X)], Proved)           :-  member([X, A], Proved).
checkLine(_, [_, or(_,B), orint2(X)], Proved)           :-  member([X, B], Proved).
checkLine(_, [_, cont, negel(P,N)], Proved)             :-  member([P, R], Proved), member([N, neg(R)], Proved).  
checkLine(_, [_, _, contel(X)], Proved)                 :-  member([X, cont], Proved).
checkLine(Prems, [_, neg(A), negint(X,Y)], Proved)      :-  getBox(X,Box,Proved),
                                                            [[X,A]|T] = Box, 
                                                            valid_proof(Prems, cont, Y, T, [[X,A]|Proved]).
checkLine(Prems, [_, A, pbc(X,Y)], Proved)              :-  getBox(X,Box,Proved),
                                                            [[X,neg(A)]|T] = Box,
                                                            valid_proof(Prems, cont, Y, T, [[X,neg(A)]|Proved]).
checkLine(_, [_, neg(neg(A)), negnegint(X)], Proved)    :-  member([X, A], Proved).
checkLine(_, [_, neg(A), mt(X,Y)], Proved)              :-  member([X, imp(A,B)], Proved), member([Y, neg(B)], Proved).
checkLine(_, [_, or(A,neg(A)), lem], _).
checkLine(_, [_, or(neg(A),A), lem], _).

getBox(AtLine, Box, Proved)                             :-  member([[AtLine,D]|T], Proved), Box = [[AtLine,D]|T].

readProof(InputFileName, Prems, Goal, Proof)            :-  see(InputFileName),
                                                            read(Prems), read(Goal), read(Proof),
                                                            seen.


