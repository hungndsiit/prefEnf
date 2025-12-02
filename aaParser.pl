:- module(aaParser,[readAAFromJsonFile/2]).


:- use_module(library(http/json)).
:- use_module(selectionFunctions).
:- use_module(pstates).
:- use_module(runtime).


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

