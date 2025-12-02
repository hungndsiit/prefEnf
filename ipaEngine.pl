:- use_module(library(http/json)).
:- use_module(selectionFunctions).
:- use_module(pstates).
:- use_module(runtime).
:- use_module(subsum).
:- use_module(preferenceDerivation).



/* parsing IPA framework from a file */

% readIPAFromJsonFile(consumerA, './tests/ipaCA.json')
readIPAFromJsonFile(HPAFID, File):- open(File, read, Stream),
				  json_read(Stream, JSON),
				  parseHPA(HPAFID, JSON),
				  preferenceCompilation(HPAFID).
				  


% Parsing AA framework from JSON object
parseHPA(HPAFID, JSON):- JSON = json(['argument base' = ArgBase, 'preference base'= PrefBase, 'queries'= Queries]),
		       retractall(hpafComponent(HPAFID,_,_)),
		       asserta(hpafComponent(HPAFID, 'argument base', ArgBase)),
		       asserta(hpafComponent(HPAFID, 'preference base', PrefBase)),
		       asserta(hpafComponent(HPAFID, 'queries',Queries)),
		       atomic_concat(HPAFID, '.base', BaseID),
		       parseAA(BaseID, ArgBase),
		       parsePB(HPAFID,PrefBase).


checkRegularExtrapolations(HPAFID):- hpafComponent(HPAFID, 'Sp',Sp),preferenceRecovery(HPAFID,R_acc,R_rej),
				     hpafComponent(HPAFID, 'queries',Queries),
				     nth0(Index, Queries, Query),
				     atomic_concat('.queryCondition#', Index, ConditionNumber),
				     atomic_concat(HPAFID, ConditionNumber, QueryConditionID),
				     Query = json(['arguments' = QueriedArguments, 'condition' = Condition]),
				     parseCondition(HPAFID,Condition, QueryConditionID),
				     member(Argument,QueriedArguments), 
				     preferenceDerivation(QueryConditionID,Sp, Argument, R), Condition=json(Description),
				     union(R_rej, R, Rleft),(subsums(Rleft,R_acc) ->
							write("("), write(Argument), write("= acc | "), write(Description), write(")");
							write("("), write(Argument), write("= rej | "), write(Description), write(")")).
				     
				       
				     
				     
    

% Preference compilation

% case 1: the choice base is empty
preferenceCompilation(HPAFID):- hpafComponent(HPAFID, 'Sp',Sp),
				hpafComponent(HPAFID, 'Experiments',Experiments),
				Experiments = [],
				retractall(hpafComponent(HPAFID,'R_acc',_)),
				asserta(hpafComponent(HPAFID, 'R_acc',[Sp])),
				retractall(hpafComponent(HPAFID,'R_rej',_)),
				asserta(hpafComponent(HPAFID, 'R_rej',[])).
				
				
% case 2: the choice base is not empty
preferenceCompilation(HPAFID):- hpafComponent(HPAFID, 'Sp',Sp),
				hpafComponent(HPAFID, 'Experiments',Experiments),
				Experiments \= [],
				findall(RofA,(member(Experiment, Experiments),
					      Experiment = (ListOfObservations, AAFID),
					      member(A='acc', ListOfObservations),
					      preferenceDerivation(AAFID,Sp, A, RofA)),List_Accepted),
				otimesList(List_Accepted, R_acc),
				retractall(hpafComponent(HPAFID,'R_acc',_)),
				asserta(hpafComponent(HPAFID, 'R_acc',R_acc)),
				findall(RofB,(member(Experiment, Experiments),
					      Experiment = (ListOfObservations, AAFID),
					      member(B='rej', ListOfObservations),
					      preferenceDerivation(AAFID,Sp, B, RofB)),List_Rejected),
				unionList(List_Rejected, R_rej),
				retractall(hpafComponent(HPAFID,'R_rej',_)),
				asserta(hpafComponent(HPAFID, 'R_rej',R_rej)).
				

% Preference Recovery: convert to logical form?

preferenceRecovery(HPAFID,R_acc, R_rej):- hpafComponent(HPAFID,'R_acc',R_acc),
					 hpafComponent(HPAFID, 'R_rej',R_rej).
					 
prettyPrint(R_acc, R_rej):- toLogicalForm(R_acc,R_rej,LogicalForm),write(LogicalForm).


% Checking regular p-satisfiability

pSatisfiable(HPAFID) :- hpafComponent(HPAFID,'R_acc',R_acc),
			hpafComponent(HPAFID, 'R_rej',R_rej),
			write(HPAFID),(subsums(R_rej,R_acc) -> writeln(" is not regular p-satisfiable"); writeln(" is regular p-satisfiable")).






% Parsing the preference base of HPA framework from JSON object PrefBase
parsePB(HPAFID,PrefBase) :- PrefBase=json(['stated preference' = Sp, 'choice base'= ChoiceBase]),
			    parseSP(HPAFID,Sp),
			    parseCB(HPAFID,ChoiceBase).





% Parsing the stated preference of HPA framework
parseSP(HPAFID,Sp) :- Sp=json(Relationships),
		      findall(PreferenceOfArgument,
		      (member(Argument = [RelationName|WithArguments], Relationships),
		      (RelationName = 'is strictly preferred to:' -> findall(strictPre(Argument,X),member(X,WithArguments),PreferenceOfArgument);
		       findall(notStrictPre(Argument,X),member(X,WithArguments),PreferenceOfArgument)
		      )),Q0),
		      unionList(Q0, Q1),
		      retractall(hpafComponent(HPAFID,'Sp',_)),
		      asserta(hpafComponent(HPAFID, 'Sp',Q1)).
		      

			    
% Parsing the choice base of HPA framework into a set of experiments ([A1=V1, A2=V2, ....],Condition)

parseCB(HPAFID,ChoiceBase):-
    findall(Experiment,(nth0(Index,ChoiceBase,Expr), atomic_concat('.expr#', Index, ExprNumber),atomic_concat(HPAFID, ExprNumber, ExprID),parseExperiment(HPAFID,Expr,ExprID,Experiment)), Experiments),
    retractall(hpafComponent(HPAFID,'Experiments',_)),
    asserta(hpafComponent(HPAFID, 'Experiments',Experiments)).

% Parse an experiment 
parseExperiment(HPAFID,Expr,ExprID,Experiment) :- Expr = json(ExprFields),
				    member('condition'=Condition, ExprFields),
				    (member('accepted'=AcceptedArguments, ExprFields) ->
					 findall(AcceptedArgument = 'acc', member(AcceptedArgument,AcceptedArguments),AcceptedObservations);
				     AcceptedObservations = []
				    ),
				    (member('rejected'=RejectedArguments, ExprFields) ->
					 findall(RejectedArgument = 'rej', member(RejectedArgument,RejectedArguments),RejectedObservations);
				     RejectedObservations = []
				    ),
				    union(AcceptedObservations,RejectedObservations,AllObservations),
				    parseCondition(HPAFID,Condition,ExprID),
				    Experiment = (AllObservations,ExprID).
				    

% Combine the condition with the ArgumentBase of HPAFID to form an AA framework identified by ExprID

parseCondition(HPAFID,Condition, ExprID) :- hpafComponent(HPAFID, 'argument base', ArgBase),
					    ArgBase = json([arguments = ArgSet, 'relations'= json(Relationships)]),
					    Condition = json(NewRelationships),
					    union(Relationships,NewRelationships,AllRelationships),
					    parseAA(ExprID,json([arguments = ArgSet, 'relations'= json(AllRelationships)])).



/* parsing AA framework from a file */

% readAAFromJsonFile(aa0, './tests/aa0.json')
readAAFromJsonFile(AAFID, File):- open(File, read, Stream),
				  json_read(Stream, JSON),
				  parseAA(AAFID, JSON).



% Parsing AA framework from JSON object
parseAA(AAFID, JSON):- JSON = json([arguments = ArgSet, 'relations'= json(Relationships)]),
		       retractall(aafComponent(AAFID,_,_)),
		       asserta(aafComponent(AAFID, 'ARG', ArgSet)),
		       forall((member(Argument = [RelationName|WithArguments], Relationships), member(X,WithArguments)),asserta(aafComponent(AAFID, RelationName, (Argument,X)))),
		       assertSpecifiedSub_arguments(AAFID),
		       computeSub_arguments(AAFID),
		       assertSpecifiedAttacks(AAFID),
		       compute_Attacks(AAFID).
		       

assertSpecifiedSub_arguments(AAFID):- retractall(specified_sub_argument(AAFID, _ , _)),
			    forall(aafComponent(AAFID, 'has sub-arguments:', (B,Bdash)), asserta(specified_sub_argument(AAFID, Bdash, B))).

% compute sub-argument closure: sub-argument relation is reflexive and transitive. NOTE: NOT YET DEAL WITH TRANSITIVE.

computeSub_arguments(AAFID) :- retractall(sub_argument(AAFID, _ , _)),
				      aafComponent(AAFID, 'ARG', ArgSet),
				      forall(member(X, ArgSet),  asserta(sub_argument(AAFID, X, X))),
				      forall(specified_sub_argument(AAFID, Bdash, B),  asserta(sub_argument(AAFID, Bdash, B))).




assertSpecifiedAttacks(AAFID):-
    retractall(specified_pd_attack(AAFID, _ , _)), retractall(specified_pi_attack(AAFID, _ , _)),
    forall(aafComponent(AAFID, 'preference-dependent attacks:', (A,B)), asserta(specified_pd_attack(AAFID, A , B))),
    forall(aafComponent(AAFID, 'preference-independent attacks:', (A,B)), asserta(specified_pi_attack(AAFID, A , B))).


%% compute the attack closure.

compute_Attacks(AAFID) :- assert_pd_direct_attacks(AAFID),
			  assert_pi_direct_attacks(AAFID),
			  assert_pd_attacks(AAFID),
			  assert_attacks(AAFID),
			  assert_pi_attacks(AAFID).
			  


%pd_direct_attack(AAFID, A , B) :- (specified_pd_attack(AAFID, A , B), \+ (specified_pd_attack(AAFID, A , Bdash), Bdash \= B, sub_argument(AAFID, Bdash, B))).
assert_pd_direct_attacks(AAFID) :- retractall(pd_direct_attack(AAFID, _ , _)),
				   forall((specified_pd_attack(AAFID, A , B), \+ (specified_pd_attack(AAFID, A , Bdash), Bdash \= B, sub_argument(AAFID, Bdash, B))), asserta(pd_direct_attack(AAFID, A , B))).


%pi_direct_attack(AAFID, A , B) :-  (specified_pi_attack(AAFID, A , B), \+ (sub_argument(AAFID, Bdash, B), Bdash \= B, specified_pi_attack(AAFID, A , Bdash))).
assert_pi_direct_attacks(AAFID) :- retractall(pi_direct_attack(AAFID, _ , _)),
    forall((specified_pi_attack(AAFID, A , B), \+ (sub_argument(AAFID, Bdash, B), Bdash \= B, specified_pi_attack(AAFID, A , Bdash))),asserta(pi_direct_attack(AAFID, A , B))).





pd_indirect_attack(AAFID, A, B) :- sub_argument(AAFID, Bdash, B), Bdash \= B, pd_direct_attack(AAFID, A , Bdash).
%pd_attack(AAFID, A, B) :- (pd_indirect_attack(AAFID, A, B); pd_direct_attack(AAFID, A , B)).
assert_pd_attacks(AAFID) :-retractall(pd_attack(AAFID, _ , _)),
    forall((pd_indirect_attack(AAFID, A, B); pd_direct_attack(AAFID, A , B)), asserta(pd_attack(AAFID, A, B))).





direct_attack(AAFID, A, B):- pi_direct_attack(AAFID, A , B); pd_direct_attack(AAFID, A , B).
indirect_attack(AAFID, A, B) :- sub_argument(AAFID, Bdash, B), Bdash \= B, direct_attack(AAFID, A, Bdash).
%attack(AAFID, A, B) :- (direct_attack(AAFID, A, B); indirect_attack(AAFID, A, B)).

assert_attacks(AAFID) :- retractall(attack(AAFID, _ , _)),
			 forall((direct_attack(AAFID, A, B); indirect_attack(AAFID, A, B)), asserta(attack(AAFID, A, B))).


%pi_attack(AAFID,A, B):- (attack(AAFID, A, B), \+ pd_attack(AAFID, A, B)).

assert_pi_attacks(AAFID) :- retractall(pi_attack(AAFID, _ , _)),
			    forall((attack(AAFID, A, B), \+ pd_attack(AAFID, A, B)),asserta(pi_attack(AAFID,A, B))).

