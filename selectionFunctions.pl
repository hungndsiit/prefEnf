:-module(selectionFunctions,[selectionFunctions/3]).


%% sl1: select X from P if P is not empty, otherwise select X from O. If P=O=empty, return null

selectionFunctions(sl1,([X|_],_,_,_),Selected) :- Selected = p(X).
selectionFunctions(sl1,([],[X|_],_,_),Selected) :- Selected = o(X).
selectionFunctions(sl1,([],[],_,_),Selected) :- Selected = null.
