:- module(subsum,[subsums/2]).
    
:- use_module(runtime).
:- use_module(pstates).

% R1 = [[notStrictPre(c,a)],[notStrictPre(b,c)],[notStrictPre(a,b)]], R2 = [[notStrictPre(c,b),notStrictPre(b,a)]], subsums(R1, R2).


% R1 = [[notStrictPre(c,a), strictPre(a,b)]], R2 = [[notStrictPre(c,a)]], subsums(R1, R2).


subsums(R1, R2):- forall(member(Q, R2),search(Q, R1, null)).
    
search(Q, R, null):-
    covers(R, Q, C),
    forall(member(X, C),(
	findall(strictPre(B,A), member(notStrictPre(B,A), X), XminusReverse),
	findall(strictPre(A,B), member(strictPre(A,B), X), Xplus),
	lub(Q, XminusReverse, Qdash),
	findall(strictPre(A,B), member(strictPre(A,B), Qdash), QdashPlus),
	(Qdash = null; s_intersection(QdashPlus,Xplus,[_|_])))).


% R1 = [[notStrictPre(c,a)],[notStrictPre(b,c)],[notStrictPre(a,b)]],Q = [notStrictPre(c,b),notStrictPre(b,a)], search(Q, R1, null).

covers(R,Q, C):- covers(R,Xs), findall(X, (member(X, Xs), s_intersection(X, Q,[])), C).
    
    
    
     
