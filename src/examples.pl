counter(Init,I):: 
   {I:Init},
   always (X,X1)$((I:X, X1 is X+1)
		 -> ({format('~p is ~p.~n',[I, X])},next {I:X1})).

