verify(InputFileName) 	:- 	readProof(InputFileName, Prems, Goal, Proof),
							checkPremises(Proof, true), 	% Nu vet vi att premises ligger endast först och inte i lådor,
															% vi vet även att alla boxar börjar med assumptions
															% TODO Assumption kan komma var som helst? Kanske fixat.
							checkEndLineNumber(Proof, Last), !,
                          	valid_proof(Prems, Goal, Last, Proof, []), !.

% Vanlig rad
checkPremises([[_,_,F]|T], LastWasPremise)              :-(F == premise, LastWasPremise, !, checkPremises(T, true));
                                                            (F \== premise, !, checkPremises(T, false)).
% Box
checkPremises([[[_,_,assumption]|BT]|T], _) 			:-	checkPremises(BT, false),
                                                            checkPremises(T, false).
checkPremises([],_).

checkEndLineNumber([_|T], Last)                         :-  checkEndLineNumber(T, Last).
checkEndLineNumber([[Last,_,_]|[]], Last).

% Last line!
valid_proof(Prems, G1, Stop, [[Stop,G2,F]|[]], Proved) 	:-  !, checkLine(Prems, [Stop,G2,F], Proved),
                                                            G1 == G2.
% Box, add to proven, prove when asked for
valid_proof(Prems, G, Stop, [[[L,D,assumption]|BT]|T], Proved)   :-  valid_proof(Prems, G, Stop, T, [[[L,D,assumption]|BT]|Proved]).

% Otherwise, usual line
valid_proof(Prems, G, Stop, [[L,D,R]|T], Proved)        :-  !, checkLine(Prems, [L, D, R], Proved), % Regeln behövs inte i Proved
                                                            valid_proof(Prems, G, Stop, T, [[L,D]|Proved]).

checkLine(Prems, [_, D, premise], _)                    :-  member(D, Prems), !.
checkLine(_, [_, B, impel(X,Y)], Proved)                :-  member([X, imp(A,B)], Proved), member([Y, A], Proved), !.
checkLine(_, [_, neg(A), mt(X,Y)], Proved)              :-  member([X, imp(A,B)], Proved), member([Y, neg(B)], Proved), !.
checkLine(_, [_, A, negnegel(X)], Proved)               :-  member([X, neg(neg(A))], Proved), !.
checkLine(_, [_, _, assumption], _).					
checkLine(_, [_, imp(A,B), impint(X,Y)], [Box|T])       :-  [[X,A,assumption]|_] = Box, valid_proof([], B, Y, Box, T).
checkLine(_, [_, B, orel(X,F1,T1,F2,T2)], [Box2,Box1|T]):-  [[F1,A1,assumption]|_] = Box1, valid_proof([], B, T1, Box1, T),
                                                            [[F2,A2,assumption]|_] = Box2, valid_proof([], B, T2, Box2, T),
                                                            (member([X, or(A1, A2)], T); member([X, or(A2, A1)], T)).
checkLine(_, [_, A, copy(X)], Proved)                   :-  member([X, A], Proved), !.
checkLine(_, [_, and(A,B), andint(X,Y)], Proved)        :-  member([X, A], Proved),
                                                            member([Y, B], Proved).
checkLine(_, [_, A, andel1(X)], Proved)                 :-  member([X, and(A,_)], Proved).
checkLine(_, [_, B, andel2(X)], Proved)                 :-  member([X, and(_,B)], Proved).
checkLine(_, [_, or(A,_), orint1(X)], Proved)           :-  member([X, A], Proved).
checkLine(_, [_, or(_,B), orint2(X)], Proved)           :-  member([X, B], Proved).
checkLine(_, [_, cont, negel(P,N)], Proved)             :-  member([P, R], Proved), member([N, neg(R)], Proved).  
checkLine(_, [_, _, contel(X)], Proved)                 :-  member([X, cont], Proved).
checkLine(_, [_, neg(A), negint(X,Y)], [Box|T])         :-  [[X,A,assumption]|_] = Box, valid_proof([], cont, Y, Box, T).
checkLine(_, [_, A, pbc(X,Y)], [Box|T])                 :-  [[X,neg(A),assumption]|_] = Box, valid_proof([], cont, Y, Box, T).
checkLine(_, [_, neg(neg(A)), negnegint(X)], Proved)    :-  member([X, A], Proved).
checkLine(_, [_, neg(A), mt(X,Y)], Proved)              :-  member([X, imp(A,B)], Proved), member([Y, neg(B)], Proved).
checkLine(_, [_, or(A,neg(A)), lem], _).
checkLine(_, [_, or(neg(A),A), lem], _).



readProof(InputFileName, Prems, Goal, Proof)            :-  see(InputFileName),
                                                            read(Prems), read(Goal), read(Proof),
                                                            seen.


