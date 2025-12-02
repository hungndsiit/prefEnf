:- module(preferenceDerivation,[constructSuccessfulAdPrefDers/3,constructSuccessfulAdPrefDers/4]).


:- use_module(library(http/json)).
:- use_module(selectionFunctions).
:- use_module(pstates).
:- use_module(runtime).

%% Assumption from user space: sub_argument/3,attack/3,pd_direct_attack/3,pi_attack/3,pd_attack/3



% case 1: an argument X is selected from P component of T = (P, O, SP, SO)
% Examples: follow(afs1, ([a],[],[],[]), [], sl1, TQPairs)
% follow(afs1, ([e], [], [e], [attack(g, a)]), [], sl1, TQPairs)
follow(AfsId, T, Q, SL, TQPairs):-
	T = (P, O, SP, SO),
	selectionFunctions(SL, T, p(X)),
	s_del_element(P,X,Pdash),
	findall(attack(Y,X), attack(AfsId, Y , X), DeltaO),
	s_union(O,DeltaO,Odash),
	SPdash = SP,
	SOdash = SO,
	Tdash = (Pdash, Odash, SPdash, SOdash), Qdash = Q,
	TQPairs = [(Tdash, Qdash)].




% case 2.a: An preference-independent attack X=(B, A) is selected from O component of  T = (P, O, SP, SO).

% T = ([], [attack(b, a), attack(c, a)], [a], []), follow(afs2, T, [], sl1, TQPairs).
follow(AfsId, T, Q, SL, TQPairs):-
	T = (P, O, SP, SO),
	selectionFunctions(SL, T, o(X)), X = attack(B, A),
	pi_attack(AfsId, B , A),
	(member(B, SP) -> TQPairs = []
	;
		findall(((Pdash, Odash, SPdash, SOdash),Qdash),
			(	attack(AfsId, C , B),
				\+ member(attack(C, B), SO), 
				\+ member(attack(C, B), O),
				(member(C, SP) -> Pdash= P;s_add_element(P,C,Pdash)),
				s_del_element(O,X,Odash),
				s_add_element(SP,C,SPdash),
				s_add_element(SO,X,SOdash),
				(pi_attack(AfsId, C , B) -> Qdash = Q
				;
				(h(AfsId,Q, B, C) -> Qdash=Q;
				(sub_argument(AfsId,Bdash, B),
				pd_direct_attack(AfsId, C , Bdash),
				lub(Q,[notStrictPre(Bdash, C)],Qdash)), Qdash \= null))
		       ),
		TQPairs)
	).

%case 2.b: An preference-dependant attack X = (B, A) is selected from component O of T = (P, O, SP, SO)

% example: T = ([], [attack(g, a)], [], []), follow(afs1, T, [], sl1, TQPairs).

follow(AfsId, T, Q, SL, TQPairs):-
	T = (P, O, SP,SO),
	selectionFunctions(SL, T, o(X)), X = attack(B, A),
	pd_attack(AfsId, B , A),
	(forall((sub_argument(AfsId,Adash, A),pd_direct_attack(AfsId, B , Adash)),member(strictPre(Adash, B),Q))
	-> 
	     Pdash = P, s_del_element(O,X,Odash), SPdash = SP, SOdash= SO, Qdash = Q,
	     TQPairs = [((Pdash, Odash, SPdash, SOdash),Qdash)]
	;
	     Pdash = P, s_del_element(O,X,Odash), SPdash = SP, SOdash= SO,
	     findall(strictPre(Adash, B),(sub_argument(AfsId,Adash, A),pd_direct_attack(AfsId, B , Adash)), DeltaQ),
	     lub(Q,DeltaQ, Qdash),
	     (Qdash = null -> FirstPair = []; FirstPair = [((Pdash, Odash, SPdash, SOdash),Qdash)]),
	     (member(B, SP) -> OtherPairs = []
	     ;

	     	     findall(((Pdash2, Odash2, SPdash2, SOdash2),Qdash2),
		      ( attack(AfsId, C , B),
			\+ member(attack(C, B), SO), 
			\+ member(attack(C, B), O),
			(member(C, SP) -> Pdash2= P;s_add_element(P,C,Pdash2)),
			s_del_element(O,X,Odash2),
			s_add_element(SP,C,SPdash2),
			s_add_element(SO,X,SOdash2),
			(pi_attack(AfsId, C , B) -> Qdash2 = Q
			;
			  sub_argument(AfsId,Bdash2, B),
			  pd_direct_attack(AfsId, C , Bdash2),
			  lub(Q,[notStrictPre(Bdash2, C)],Qdash2), Qdash2 \= null
			)),
		      OtherPairs)
		     
	     ),
	     s_union(OtherPairs,FirstPair,TQPairs)
	).


h(AfsId,Q, B, C):- sub_argument(AfsId,Bdash, B), pd_direct_attack(AfsId, C , Bdash), member(strictPre(C, Bdash),Q),!.


% preferenceDerivation(aa0,[], J, Rfinal).

%preferenceDerivation(AfsId,Q0, A, Rfinal):-
%%	while(AfsId, [(([A],[],[A],[]),Q0)], [], R), simplify(R, Rfinal).
	

%% need to turn this while loop into tail recursion

while(AfsId, MT, R, Rfinal):-
	(MT = [] -> Rfinal = R
	;
		MT = [(T,Q) | Others],
		(T = ([],[],_, _) -> 
			while(AfsId, Others, R, Rfinaldash),
			s_add_element(Rfinaldash,(T, Q),Rfinal)
		;
			follow(AfsId, T, Q, sl1, TQPairs),
			s_union(TQPairs,Others,MTdash),
			while(AfsId, MTdash, R, Rfinal)
		)
	).


while(AfsId,E,  MT, R, Rfinal):-
	(MT = [] -> Rfinal = R
	;
		MT = [(T,Q) | Others],
		(T = ([],[],_, _) -> 
			while(AfsId, E, Others, R, Rfinaldash),
			s_add_element(Rfinaldash,(T, Q),Rfinal)
		;
	       	        follow(AfsId, T, Q, sl1, TQPairs),
		        findall(TQPair, (member(TQPair, TQPairs), TQPair = (Tdash, _), Tdash = (_,_, E,_)),FilteredTQPairs),
			s_union(FilteredTQPairs,Others,MTdash),
			while(AfsId, E, MTdash, R, Rfinal)
		)
	).




%% Algorithm 4: Construct successful preference derivations.
%% Input: a set  MT  of preference-derivation states; a function Follow

%% sample all: constructSuccessfulAdPrefDers(aa0,[((['E1'],[],['E1'],[]),[])], R)

constructSuccessfulAdPrefDers(AfsId,MT, R) :-
    while(AfsId, MT, [], R).



constructSuccessfulAdPrefDers(AfsId, E, MT, R) :-
    while(AfsId, E, MT, [], R).
