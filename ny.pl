verify(InputFileName) 	:- 	readProof(InputFileName, Prems, Goal, Proof),
							checkPremises(Proof, true), 	% Nu vet vi att premises ligger endast först och inte i lådor,
															% vi vet även att alla boxar börjar med assumptions
															% TODO Assumption kan komma var som helst? Kanske fixat.
							checkEndLineNumber(Proof, Last), !,
                          	valid_proof(Prems, Goal, Last, Proof, []).

% Vanlig rad
checkPremises([[_,_,F]|T], LastWasPremise)				:-	(F == premise, LastWasPremise, !, checkPremises(T, true));
                                                            (F \== premise, !, checkPremises(T, false)).
% Box
checkPremises([[[_,_,assumption]|BT]|T], _) 			:-	checkPremises(BT, false),
                                                            checkPremises(T, false).
checkPremises([],_).

checkEndLineNumber([_|T], Last)                         :-	checkEndLineNumber(T, Last).
checkEndLineNumber([[Last,_,_]|[]], Last).

% Last line!
valid_proof(Prems, G1, Stop, [[Stop,G2,F]|[]], Proved) 	:-	!, checkLine(Prems, [Stop,G2,F], Proved),
															G1 == G2.
% Otherwise, usual line
valid_proof(Prems, G, Stop, [[L,D,R]|T], Proved)		:- 	!, checkLine(Prems, [L, D, R], Proved), % Regeln behövs inte i Proved
															valid_proof(Prems, G, Stop, T, [[L,D]|Proved]).
% Box, add to proven, prove when asked for
valid_proof(Prems, G, Stop, [[[L,D,assumption]|BT]|T], Proved)	:-	valid_proof(Prems, G, Stop, T, [[[L,D,assumption]|BT]|Proved]).

checkLine(Prems, [_, D, premise], _)					:-	member(D, Prems), !.
checkLine(_	, [_, B, impel(X,Y)], Proved)				:-	member([X, imp(A,B)], Proved), member([Y, A], Proved), !.
checkLine(_		, [_, neg(A), mt(X,Y)], Proved)			:-	member([X, imp(A,B)], Proved), member([Y, neg(B)], Proved), !.
checkLine(_, [_, A, negnegel(X)], Proved)				:-	member([X, neg(neg(A))], Proved), !.
checkLine(_	, [_, _, assumption], _).					
checkLine(_, [_, imp(A,B), impint(X,Y)], [Box|T])       :-	[[X,A,assumption]|_] = Box, valid_proof([], B, Y, Box, T).


readProof(InputFileName, Prems, Goal, Proof) 			:- 	see(InputFileName),
                                                            read(Prems), read(Goal), read(Proof),
                                                            seen.


