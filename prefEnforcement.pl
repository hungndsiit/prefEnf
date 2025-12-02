:- use_module(library(http/json)).
:- use_module(selectionFunctions).
:- use_module(pstates).
:- use_module(runtime).
:- use_module(subsum).
:- use_module(preferenceDerivation).
:- use_module(transform).

:- discontiguous prefExtEnf/5.

/* interface of enforcement algorithms*/

%% Simplify the ouput

prefExtEnf(P1, P2,P3, P4, SimR, simpl) :- prefExtEnf(P1, P2,P3, P4, Rout),simplify(Rout,SimR).

%% Algorithm 5:

%% Sample call: prefExtEnf(sb, ad, aa0, ['E1'], PrefStateSet).

prefExtEnf(sb, ad,AAFID, E, Rout) :-
    T0 = (E, [],E,[]), Q0 = [],
    constructSuccessfulAdPrefDers(AAFID,[(T0,Q0)],PDStates),
    findall(Q, member((_, Q), PDStates), Rout).
    %simplify(R, Rout).


%% Algorithm 6:

%% Sample call:  prefExtEnf(sb, ad, aa0, ['E1'], R).

prefExtEnf(fl, ad,AAFID, E, Rout) :-
    T0 = (E, [],E,[]), Q0 = [],
    constructSuccessfulAdPrefDers(AAFID,E,[(T0,Q0)],PDStates),
    findall(Q, member((_, Q), PDStates), Rout).
    %simplify(R, Rout).


prefExtEnf(sb, pr,AAFID, E, Rout) :-  prefExtEnf(sb, ad,AAFID, E, Rout).


%% Algorithm 7

%% sample call: prefExtEnf(sl, pr,aa0, ['A1','A2'],MQstar).

prefExtEnf(sl, pr,AAFID, E,MQstar):-
    % Generation step:
    prefExtEnf(fl, ad, AAFID, E, MQtemp), simplify(MQtemp,MQ),
    % Exclusion step:
    findall((Qi, MQi),(member(Qi,MQ),compute(AAFID,E, Qi,MQitemp),simplify(MQitemp,MQi)),ListOfPairQiMQi),
    % Simplification step
    findall(MQjStar,(member((Qj,MQj),ListOfPairQiMQi), transf(Qj,MQj,MQjStar)),SetOfMQjStar),
    general_union(SetOfMQjStar,MQstar).



compute(AAFID,E, Qi, MQi):-
    aafComponent(AAFID,'ARG',Arg),
    s_subtract(Arg, E, OtherArguments),
    findall((([X],[],[X],[]),Qi),member(X, OtherArguments),MT),
    constructSuccessfulAdPrefDers(AAFID,MT,MRi),
    findall(Q, member((_, Q), MRi),MQ),
    simplify(MQ, MQi).




%% Algorithm 8

%% sample call: prefExtEnf(fl, pr,aa0, ['E1', 'X1', 'A2'],MQstar).


prefExtEnf(fl, pr,AAFID, E,MQstar):-
    % generation
    prefExtEnf2(fl, ad,AAFID, E, MR),
    % exclusion
    aafComponent(AAFID,'ARG',Arg),
    s_subtract(Arg, E, OtherArguments),
    findall((Qi,MQi),(
		member((Ti,Qi),MR),Ti = ([],[],E,SOi),
		findall((([X],[],E,SOi),Qi),member(X,OtherArguments),MTi),
		constructSuccessfulAdPrefDers(AAFID,MTi,MRi),
		findall(Q,(member((_,Q),MRi)),MQitemp),simplify(MQitemp,MQi)),ListOfPairQiMQi),				    
     % Simplification step
    findall(MQjStar,(member((Qj,MQj),ListOfPairQiMQi), transf(Qj,MQj,MQjStar)),SetOfMQjStar),
    general_union(SetOfMQjStar,MQstar).
    



% same as prefExtEnf, but return also the set of whole preference-derivation states
% sample calls: prefExtEnf2(fl, ad,aa0, ['E1','X1','A2'], PDStates) 

prefExtEnf2(fl, ad,AAFID, E, PDStates) :-
    T0 = (E, [],E,[]), Q0 = [],
    constructSuccessfulAdPrefDers(AAFID,E,[(T0,Q0)],PDStates).






/* parsing AFS framework from a file */

% readAAFromJsonFile(aa0, './tests/aa0.json')
readAAFromJsonFile(AAFID, File):- open(File, read, Stream),
				  json_read(Stream, JSON),
				  parseAA(AAFID, JSON).


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

% compute sub-argument closure: sub-argument relation is reflexive and transitive.

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

