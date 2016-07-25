/* A Prolog interpreter for Timed Gentzen.
   (c) Vijay Saraswat, 1995
   See the paper
     Vijay Saraswat, Radha Jagadeesan, Vineet Gupta 
    "Programming in Timed Concurrent Constraint Programming",
   (c) IBM 2016
*/

:- op(1100, xfy, '::').
:- op(975, fy, [next, always]).
:- op(950, xfy, [ '->' , '~>']). % Note: ~> is weak else. 
:- op(150, xfy, ['^', '$']).
:- use_module(library(ordsets)).
:- use_module(library(lists)).

tcc((A,Pool)):- !, tcc(A, Pool, [true, a([],true), true, true, 0, 0]).
tcc(A)       :-    tcc((A, true)).

/* tcc(Agents, State) :-
     run the Agents in the given State.
     State = [Store, SuspendedAgents, ElseAgents, NextAgents, Iteration, ExVarCount]
*/
:- discontiguous tcc/2.
tcc(true, [Store, _SuspA, Elses, Next, C, _V]):- !,
    next(Elses, Store, Next, New),
    termination(New, C).
tcc((A,Pool), State):- !,tcc(A, Pool, State).
tcc(A,        State):-   tcc((A,true), State).

termination(true, C):- !, format('Termination at T=~p.~n', [C]).
termination(A,C):- C1 is C+1,
	my_debug('Moving to T=~p.~n', [C1]),
	tcc(A, [true, a([], true), true, true, C1, 0]).

:-dynamic debug/0.

my_debug(S,L):- debug,!, format(S,L).
my_debug(_S,_L).
portray(tcc(Agent,Pool,[Store,Susp,Else,Next,Iter,ECount])) :-
       format('tcc/3:~n',[]),
	format(' Agent:~p~n',[Agent]),
	format(' Pool:~p~n',[Pool]),
	format(' Store:~p~n',[Store]),
	format(' Susp:~p~n',[Susp]),
	format(' ElseNext:~p~n',[Else]),
	format(' Next:~p~n',[Next]),
	format(' Iter:~p~n',[Iter]),
	format(' EVar Count:~p~n',[ECount]).

portray(tcc(Agent,[Store,Susp,Else,Next,Iter,ECount])) :-
       format('tcc/2:~n',[]),
	format(' Agent:~p~n',[Agent]),
	format(' Store:~p~n',[Store]),
	format(' Susp:~p~n',[Susp]),
	format(' ElseNext:~p~n',[Else]),
	format(' Next:~p~n',[Next]),
	format(' Iter:~p~n',[Iter]),
	format(' EVar Count:~p~n',[ECount]).


tcc({(A, B)}, Pool, State) :-!, tcc({A}, ({B},Pool), State).
tcc({C}, Pool, [Store, SuspA | Rest]) :-!,
	install_tell(C, Pool, Store, SuspA, NewPool, NewStore),
	tcc(NewPool, [NewStore, SuspA | Rest]).

tcc((E1,E2) -> A, Pool, State) :-!, tcc(E1 -> E2 -> A, Pool,           State).
tcc((E1;E2) -> A, Pool, State) :-!, tcc(E1 -> A,       (E2 -> A,Pool), State).
tcc(C -> A, Pool, [Store, SuspA|Rest]) :-!,
	install_ask(C -> A, Pool, Store, SuspA, NewPool, NewSuspA),
	tcc(NewPool, [Store, NewSuspA|Rest]).

tcc(E ~> A, Pool, [Store, SuspA, Elses | Rest]) :-!,
	tcc(Pool, [Store, SuspA, (E~>A,Elses) | Rest]).

tcc(next A, Pool, [Store, SuspA, Elses, Nexts | Rest]) :-!,
	tcc(Pool, [Store, SuspA, Elses, (A,Nexts) | Rest]).

tcc(_X$A, Pool, State) :-!, tcc(A, Pool, State).

tcc(Vars^A,Pool,[Store,SuspA,Elses,Nexts,C,V]) :-!,
	inst_ex_vars(Vars,C,V,NV),
	tcc(A,Pool,[Store,SuspA,Elses,Nexts,C,NV]).

tcc(abort, _Pool, _State) :-!, format('Aborting.~n',[]), fail.

tcc(true,  Pool,State) :-!, tcc(Pool,State).
tcc((A, B),Pool,State) :-!, tcc(A,(B,Pool),State).
tcc(Goal,  Pool,State) :-(Goal :: Body), !, tcc(Body,Pool,State).


%----- install_ask
portray(install_ask(Ask,Pool,Store,Susp,NewPool,NewSusp)) :-
       format('install_ask:~n',[]),
	format(' Ask:~p~n',[Ask]),
	format(' Pool:~p~n',[Pool]),
	format(' Store:~p~n',[Store]),
	format(' Susp:~p~n',[Susp]),
	format_diff(' NewPool:~p~n',NewPool,' NewPool=Pool~n',Pool),
	format_diff(' NewSusp:~p~n',NewSusp,' NewSusp=Susp~n',Susp).

format_diff(_S,X,OS,Y):- X==Y, !, format(OS,[]).
format_diff(S,X,_OS,_Y):- format(S,[X]).

install_ask(C->A,Pool,Store,a(Var,SuspA),NewPool,NewSusp) :-
	ask_basic(C)
	-> (NewSusp=a(Var, SuspA), (call(C) -> NewPool=(A,Pool);NewPool=Pool))
	; (vars(A, C, Var, VC, Vs, NewVar),
	   (VC==[]
	   -> (my_member(C, Store)
	      -> (NewPool=(A,Pool), NewSusp=a(Var,          SuspA))
	      ;  (NewPool=   Pool,  NewSusp=a(NewVar, (C->A,SuspA))))
	   ; (NewSusp=a(NewVar, (C->A,SuspA)),
	      (bagof(A, Vs^my_member(C, Store), Agents)
	       -> (commaify(Agents, CAgents), NewPool=(CAgents,Pool)); NewPool=Pool)))).

my_member(C, (C,_Rest)):- !.
my_member(C, (_,Rest)):- my_member(C, Rest).

commaify([],true).
commaify([X|Xs],(X,Ys)):- commaify(Xs,Ys).

ask_basic((_X :: _Y)).
ask_basic( _X is _Y).
ask_basic( _X =:= _Y).
ask_basic( _X< _Y).
ask_basic( _X =< _Y).
ask_basic( _X = _Y).
ask_basic( _X >= _Y).
ask_basic( _X > _Y).
ask_basic(read(_X)).
ask_basic(call(_)).
ask_basic(proc(X)).

/**
  proc(Goal):-
     Goal is a call to a user-defined TG procedure.

  User must not define caluses for ask_basic, ask_tell functors, or ,/2.
  */
proc(Goal):-
	nonvar(Goal),
	\+(ask_basic(Goal)),
	functor(Goal,F,A),  % must not be a conjunction
	\+((F==',',A==2)).

/* vars(A, C, Var, VC, Vs, NewVar) :-
  Given terms A and C, var set Var,
    VC = vars(C), VA = vars(A),
    Vs = VC \ VA,
    NewVar = Var U VA U VC.
*/ 
vars(A, C, Var, VC, Vs, NewVar) :-
	vars(A, VA),
	vars(C, VC),
	ord_subtract(VC, VA, Vs),
	ord_union(VA, VC, Vars1),
	ord_union(Vars1, Var, NewVar).

% vars(Term, Vars):- Vars is the ordset of all variables in Term.
vars(Term,Vars) :- vars(Term,[],Vars).

vars(   X,V,Vars) :- var(X), !, ord_add_element(V, X, Vars).
vars(Term,V,Vars) :- 
	functor(Term, _F, A),
	vars_each(0, A, Term, V, Vars).

vars_each(M,M,_Arg,V,V).
vars_each(M,N, Arg,V,Vars):- M < N, 
	M1 is M+1,
	arg(M1,Arg,Term),
	vars(Term,Var1),
	ord_union(Var1,V,Var2),
	vars_each(M1,N,Arg,Var2,Vars).

% Tell processing
portray(install_tell(Tell,Pool,Store,Susp,NewPool,NewStore)) :-
       format('install_tell:~n',[]),
	format(' Tell:~p~n',[Tell]),
	format(' Pool:~p~n',[Pool]),
	format(' Store:~p~n',[Store]),
	format(' Susp:~p~n',[Susp]),
	format_diff(' NewPool:~p~n',NewPool,' NewPool=Pool~n',Pool),
	format_diff(' NewStore:~p~n',NewStore, ' NewStore=Store~n',Store).

install_tell(C,Pool,Store,a(Vars,SuspA),NewPool,NewStore) :-
	tell_basic(C)
	-> (call(C), NewStore=Store, NewPool=Pool)
	; (my_member(C, Store)
	  -> (NewStore=Store, NewPool=Pool)
	  ; (NewStore=(C,Store), my_debug('Added ~p to store.~n',[C]),
	     (bagof(A, Vars^my_member(C->A, SuspA), Agents)
	     -> (commaify(Agents, CAgents), NewPool=(CAgents,Pool))
	     ;  NewPool=        Pool))).
                               
tell_basic(format(_X,_Y)).
tell_basic(ttyflush).
tell_basic(call(_X)).

% Negative ask processing -- weak defaults only. 
next(true,          _Store, Next, Next).
next((C~>A,E), Store, Next, Out) :- !,
	(succeeds(C, Store)  % need to just check once.
	-> next(E, Store, Next, Out)
	; (Out=(A,Out1), next(E, Store, Next, Out1))).

succeeds((C1,C2), Store) :- !, succeeds(C1, Store), succeeds(C2, Store).
succeeds((C1;C2), Store) :- !, (succeeds(C1, Store) ; succeeds(C2, Store)).
succeeds(C,       Store) :- ask_basic(C) -> call(C) ; my_member(C, Store).

% Existential quantification processing

/* inst_ex_vars(Vars, C, V, NV):-
    Instantiate each var in Vars to a _(C, V') term, where V' is
    the next constant available, after V. NV is the last used value.
*/
inst_ex_vars([],_C,V,V).
inst_ex_vars([X|Rest],C,V,NewV):-
	X =..['_',C,V],
	V1 is V+1,
	inst_ex_vars(Rest,C,V1,NewV).

:-ensure_loaded(combinators).
