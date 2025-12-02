:-module(runtime,[s_subset/2, s_empty/1, s_memberchk/2, s_union/3,general_union/2, s_intersection/3, s_subtract/3, s_add_element/3, s_del_element/3, ms_empty/1, ms_memberchk/2, ms_union/3, ms_add_element/3, ms_del_element/3, succ/1,singletonize/2, covers/2, base/3]).


%% envi module
%% Purpose: define the set of operations that runtime of PABA should
%% provide. No other operations are assumed.
%% There are two kinds of operations: set operations, prefixed by s_;
%% and multi set operations, prefixed by ms_


%% Prolog engine, like SWIPL, often offers list operations. Hence in
%% SWIPL, set operations as well as multi-set operations are implemented
%% by list operations

%% set is list
%% Examples: [] is empty set, [1,2] is set containing two elements


%% multiset is list
%% Interp. multiset allow element repitions, but the order does not
%% matter
%% Examples: [1,1,2] is a multi set containing two occurences of 1


%% set -> boolean
%% check if set S is empty
%% Example: s_empty([]) is true, s_empty([1]) is false

s_empty(S):- ord_empty(S).


%% any set -> boolean
%% check if element E is a member of set S.
%% Example: s_member(1,[1,2]) is true
%
s_memberchk(E,S) :- memberchk(E,S).

%% set set -> set
%% union two set
%% Example. s_union([1,2],[1,3],[1,2,3])
s_union(S1,S2,U):- union(S1,S2,U).

general_union([],[]).
general_union([Set|OtherSets],All) :- general_union(OtherSets,U), s_union(Set,U,All).
    

%% set set -> set
%% intersect two sets
s_intersection(S1,S2,I) :- intersection(S1,S2,I).

%% set set -> set
%% produce R = S \ D

s_subtract(S,D,R) :- subtract(S,D,R).

%% set any -> set
%% add element E into S to obtain N
s_add_element(S,E,N):- (member(E, S) -> N=S;s_union(S,[E],N)).

%% set any -> set
%% remove element E from set S to obtain N
s_del_element(S,E,N) :- s_subtract(S,[E],N).

%% set set -> boolean
%% produce true if Sub is a supet of Super
s_subset(Sub,Super) :- subset(Sub,Super).



%%%% Ulti functions for Skeptical acceptance

%% set -> set of singletons

singletonize(S, R) :- findall([E], member(E, S), R).

%% set of set -> set of set
%% covers(B), where B is a set of set, is {O| O is a minimal set such that O \cap S \neq empty for each S \in B}
%% Example: covers([[1,2],[3,4,1,1]], R) return R = [[1], [2, 3], [2, 4]]


cover(C,[],C).

cover(Cin,[A|Others],Cout):-
    expand(Cin,A,Ctemp),
    cover(Ctemp,Others,Cout).


expand(Cin,A,Cout):- (s_intersection(Cin,A,[]) -> member(E,A), s_add_element(Cin,E,Cout); Cout=Cin).

coverSet(Base,Covers):-findall(C,(cover([],Base,C)),Covers).

minimize(Covers,XB):-findall(C,(member(C,Covers),minimal_cover(C,Covers)),XB).

minimal_cover(C,Covers):- \+ not_minimal(C,Covers).

not_minimal(C,Covers):- member(E,Covers), strict_supset(C,E),!.

strict_supset(C,E) :- s_subset(E,C), \+ E=C.


covers(Base,XB) :- coverSet(Base,Covers), minimize(Covers,XB).


%% retrieve base

base(S, Scal, BaseOfS) :-
    findall(A,member((([],[],A,_),S), Scal), BaseOfS).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%% multi-set operations%%%%%%%%%%%%%%%%%%%%

%% multiset -> true
%% produce true just in case S is an empty set
ms_empty(S):- ord_empty(S).

%% multiset -> boolean
%% produce true if E is an element of multiset S
ms_memberchk(E,S) :- memberchk(E,S).

%% multiset multiset -> multiset
%% union two multisets

ms_union(S1,S2,U):- append(S1,S2,U).

%% multiset any -> multiset
%% add an element E to multiset S to obtain multiset N
ms_add_element(S,E,N):- append([E],S,N).

%% multiset any -> multiset
%% delete all occurences of E in S to obtain N
ms_del_element(S,E,N) :- delete(S,E,N).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% proposition is atom
%% tuple is
%% (multiset<propostion>,set<multiset<proposition>,set<proposition>,set<proposition>)
%%
%%
%
%% Interp. tuple (P,O,A,C) represents ...with
%%        - P represents the proponent nodes;
%%	  - O represents the opponent nodes;
%%	  - A represents proponent's assumptions;
%%        - C represents culprit sets

%% Examples:
%%     t0 = ([a], [], [a], [])
%%     t1 = ([], [[not(a)]], [a], [])
%%     t2 = ([], [[g]], [a], [])
%%


%% Some useful functions working on tuples
%% tuple -> boolean
%% true only if t has the form ([],[],_,_)
succ(([],[],_,_)).








