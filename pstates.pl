
:-module(pstates,[lub/3, simplify/2,queryAnswer/3,otimesList/2,unionList/2,toLogicalForm/3,negate/2]).

:- use_module(runtime).
:- use_module(subsum).

% negation of a preference statement

negate(strictPre(A, B),notStrictPre(A, B)).
negate(notStrictPre(A, B),strictPre(A, B)).


% HatQ is a logical conjuctive formula representing a preference state Q
hatQ(Q, HatQ):- (Q = [] -> HatQ = 'True';
		 (Q = [H] -> (H = strictPre(A,B) -> term_string((A>B),HatQ); H = notStrictPre(A,B), term_string(not(A>B),HatQ));
		 Q = [H|Q1], hatQ([H],HatH), hatQ(Q1,HatQ1), string_concat(HatH, ' and ', Hand), string_concat(Hand, HatQ1, LHatQ),
		 string_concat("(", LHatQ, OHatQ),string_concat(OHatQ, ")", HatQ))
		).   


notHatQ(Q,NHQ) :- (Q =  [] -> NHQ = 'False' ;
		   Q = [H] ->
		       (H = strictPre(A,B) -> term_string(not(A>B),NHQ); H = notStrictPre(A,B), term_string((A>B),NHQ));
		   Q = [H|Q1], notHatQ([H],NHatH), notHatQ(Q1,NHatQ1), string_concat(NHatH, ' or ', NHatHOr), string_concat(NHatHOr, NHatQ1, LNHQ),
		   string_concat("(", LNHQ, OLNHQ),string_concat(OLNHQ, ")", NHQ)
		   ).

% interpreting a set of preference states R containing Q as a DNF of HatQ
dnf(R_acc,DNF):- (R_acc = [Q] ->
		  hatQ(Q,HatQ), DNF = HatQ;
		  R_acc = [Q|R], hatQ(Q,HatQ), dnf(R,DNFR), string_concat(HatQ, ' or ' , HatQor), string_concat(HatQor, DNFR , DNF)). 

negCNF(R_rej,NCNF):- (R_rej = [Q] -> notHatQ(Q,NHQ), NCNF = NHQ;
		      R_rej = [Q|R], notHatQ(Q, NotHatQ),string_concat(NotHatQ, " and ", NotHatQand),negCNF(R,NCNFR), string_concat(NotHatQand, NCNFR,NCNF)
		     ).

toLogicalForm(R_acc,R_rej,LogicalForm) :- dnf(R_acc,DNF1),
					  string_concat("\n==================\nRecovered preference implies:\n\n ", DNF1, String1),
					  (R_rej \= [] -> negCNF(R_rej,NCNF),
							  string_concat(String1, "\n\n and should not contradict with: \n\n", String2),
							  string_concat(String2, NCNF, String3),string_concat(String3, "\n===================\n",LogicalForm);
					                  string_concat(String1, "\n===================\n",LogicalForm)
					   ).
					  

% check if Q1 implies Q2

% Q1= [strictPre(a,b),strictPre(a,c),strictPre(b,c)], Q2 = [notStrictPre(c,b),strictPre(a,c),strictPre(a,b)], implies(Q1,Q2)


%% M(Q1) is a subset of M(Q2) if any statement in Q2 is also in Q1; or it is a negative notStrictPre(C, D) where D>C is in Q1


implies(Q1,Q2) :- forall(member(strictPre(A, B), Q2), member(strictPre(A, B), Q1)),
		  forall(member(notStrictPre(C, D), Q2), (member(notStrictPre(C, D), Q1); member(strictPre(D, C), Q1))).


removeRedundantNegativeStatements(Q1,Q2):- findall(N, (member(N, Q1), N = notStrictPre(X, Y), member(strictPre(Y, X), Q1)), AN),
					   s_subtract(Q1,AN,Q2).


% Q1= [strictPre(a,b),strictPre(a,c),strictPre(b,c)], Q2 = [notStrictPre(c,b),strictPre(a,c),strictPre(a,b)], equavalent([Q1, Q2], R2)


%% removing Q1 since M(Q1) is a subset of M(Q2)

equivalent(R1, R2):- ((member(Q1, R1), member(Q2,R1), Q1 \= Q2, implies(Q1, Q2)) -> s_del_element(R1,Q1,R2); R1=R2).


% Q1= [strictPre(a,b),strictPre(a,c),strictPre(b,c)], Q2 = [notStrictPre(c,b),strictPre(a,c),strictPre(a,b)], simplify([Q1, Q2], R2)


simplify1(R1, R2) :- equivalent(R1, R3), (R1 = R3 -> R2=R3; simplify1(R3, R2)).

simplify(R1,R3) :- simplify1(R1, R2), findall(Qdash, (member(Q, R2),removeRedundantNegativeStatements(Q,Qdash)),R3).  


%  otimes([R1, R2, ..., Rn], R)
% examples R1= [[strictPre(a,b)]], R2= [[strictPre(b,c)],[notStrictPre(c,d)]], otimesList([R1, R2], R).

% preferenceDerivation('caf.experiment#4', a, R), preferenceDerivation('caf.experiment#0', a, Ra),  preferenceDerivation('caf.experiment#2', b, Rb2, otimesList([R, Ra, Rb2], Left).

otimesList([], [[]]).
otimesList([R1|R2n], R) :- otimesList(R2n, Rdash), otimesBinary(R1, Rdash, R).
otimesBinary(R1, R2, R) :- findall(Q, (member(Q1, R1), member(Q2, R2), lub(Q1, Q2, Q), Q \= null), R) .


% R1= [[strictPre(a,b)]], R2= [[strictPre(c,b)],[notStrictPre(c,d)]], unionList([R1, R2], R).

unionList([], []).
unionList([R1|R2n], R) :- unionList(R2n, Rdash), union(R1, Rdash, Rdash2), list_to_set(Rdash2, R).


% R = [[]], List_R1_to_Rn = [[[]]], List_to_Rm = [[[]]],  queryAnswer(R, List_R1_to_Rn, List_to_Rm).

queryAnswer(R, R_acc, R_rej):-
    unionList([R,R_rej], Left),Right = R_acc,
    write("Checking if Left = "), write(Left), write("\n subsums Right = "), write(Right),
    (subsums(Left,Right) -> write("\nSubsumption passed ==> the argument is accepted")
    ; write("\n Subsumption fails ==> the argument is not accepted")). 




% Example: preferenceDerivation('caf.experiment#4', a, R), preferenceDerivation('caf.experiment#0', a, Ra), preferenceDerivation('caf.experiment#1', b, Rb1), preferenceDerivation('caf.experiment#2', b, Rb2), preferenceDerivation('caf.experiment#3', c, Rc), preferenceDerivation('caf.experiment#0', a, Ra), List_Accepted = [Ra, Rb2],  List_Rejected = [Rb1, Rc],  queryAnswer(R, List_Accepted, List_Rejected).





% least upper bound of two preference states Q1 and Q2



% check if Q is consistent according to Def 15.b
% example: consistent([strictPre(a,b), notStrictPre(a,b)]) is not consistent

consistent(Q) :- findall(notStrictPre(A, B), member(notStrictPre(A, B), Q), Qminus),
		 forall(member(strictPre(A, B), Q),\+ member(notStrictPre(A, B), Qminus)).

% check if Qplus is asymmetric
% Example: asymmetric([strictPre(a, b), strictPre(b, a)]) should be False

asymmetric(Q) :- \+ (member(strictPre(A, B), Q), member(strictPre(B, A), Q)).

% check if Qplus is transitive

% Example: transitive([strictPre(a, b), strictPre(b, c), strictPre(a,c)]) is True

transitive(Q) :- forall((member(strictPre(A, B), Q),member(strictPre(B, C), Q)),
			member(strictPre(A, C), Q)).



% Q = [strictPre(a, b), strictPre(b, c), strictPre(a,c)], strictPreList(Q, a, L).
strictPreList(Q, A, L) :- findall(B, member(strictPre(A, B), Q),L).

%  Q = [strictPre(a, b), strictPre(b, c), strictPre(a,c)],argument(Q, X).

argument(Q, A):- member(strictPre(A,_), Q);
		 member(strictPre(_,A), Q);
		 member(notStrictPre(A,_), Q);
		 member(notStrictPre(_,A), Q).

%  Q = [strictPre(a, b), strictPre(b, c), strictPre(a,c), notStrictPre(e,f)],argumentSet(Q,ARG).
argumentSet(Q,ARG) :- findall(X, argument(Q,X), As), list_to_set(As, ARG). 


% %  Q = [strictPre(a, b), strictPre(b, c), strictPre(a,c), notStrictPre(e,f)],ugraph(Q,ARG)

ugraph(Q,Graph) :- argumentSet(Q,ARG), findall(A-L, (member(A,ARG), strictPreList(Q,A,L)),Graph).


% Q = [strictPre(a, b), strictPre(b, c), notStrictPre(e,f)],transitiveClosure(Q,Closure).

transitiveClosure(Q,Closure) :- ugraph(Q,Graph), transitive_closure(Graph,Closure).


%  Q = [strictPre(a, b), strictPre(b, c), notStrictPre(e,f)],transitiveClosure(Q,Closure), ugraphToPreState(Closure, State).

ugraphToPreState(Graph, State) :- findall(strictPre(A, B), (member(A-L, Graph), member(B, L)), State).


% Q1 = [strictPre(c, a)], Q2 = [strictPre(c,b)], lub(Q1, Q2, Q).

lub(Q1, Q2, Q):-
    union(Q1, Q2, Qtemp),
    findall(strictPre(A, B), member(strictPre(A, B), Qtemp), Qplus),
    findall(notStrictPre(C, D), member(notStrictPre(C, D), Qtemp), Qminus),
    transitiveClosure(Qplus,Ugraph), ugraphToPreState(Ugraph, State),
    %findall(notStrictPre(A, B), (member(notStrictPre(A, B),Qminus), member(strictPre(B, A), State)), QminusDash),
    union(Qminus, State, Qdash),
    ((consistent(Qdash),asymmetric(Qdash)) -> Q= Qdash; Q = null). 
    
    

