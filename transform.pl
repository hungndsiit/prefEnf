:- module(transform,[transf/3]).
    
:- use_module(runtime).
:- use_module(pstates).



% computeMS([notStrictPre('X1','A1')], [[notStrictPre('X1','A1'),notStrictPre('A1','X1')],[notStrictPre('X1','A1'),notStrictPre('A2','X1')]],MS)

computeMS(R, MR,MS):- findall(RiMinusR,(member(Ri, MR),s_subtract(Ri,R,RiMinusR)),Base),
		      covers(Base,XB),findall(CB,(member(B, XB),negateAll(B, CB)),MS).

negateAll(B, CB) :- findall(Y, (member(X, B), negate(X,Y)),CB).


% R = [notStrictPre('X1','A1')], MR =  [[notStrictPre('X1','A1'),notStrictPre('A1','X1')],[notStrictPre('X1','A1'),notStrictPre('A2','X1')]], transf(R, MR,MRStar).
transf(R, MR,MRStar):- computeMS(R, MR,MS),
		       findall(RfusedwithS,(member(S, MS), lub(R, S, RfusedwithS)), MRStarTemp),
		       findall(X, (member(X,MRStarTemp), X \= null),MRStar).
    
     
