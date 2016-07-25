/* A Prolog interpreter for Timed Gentzen.
   (c) Vijay Saraswat, 1995
   See the paper
     Vijay Saraswat, Radha Jagadeesan, Vineet Gupta 
    "Programming in Timed Concurrent Constraint Programming",
   (c) IBM 2016
*/

always A:: A, next always A.

if(Cond, Then, Else) :: [Cond -> Then, Cond ~> Else].

/**
  Run A the first time that C holds.
*/

whenever(C,A) :: C -> A, C ~> whenever(C, A).

watching(_C,D)     :: D.
watching(C,D->A)   :: D -> watching(C,A). 
watching(C,D~>A)   :: (C;D) ~> watching(C,A).
watching(C,next A) :: C~>watching(C,A).
watching(C,Vars^A) :: Vars^watching(C,A).
watching(C,_Vars$A):: watching(C,A).

watching(_C, abort):: abort.
watching(_C, true) :: true.
watching(C, (A,R)) :: watching(C,A),watching(C,R).
watching(C, A)     :: proc(A) -> Body$((A :: Body) -> watching(C, Body)).

/*time_on(C, A) :: clock(always(C), A).
do_watching(C, A) :: clock(whenever(C, (next abort)), A).
susp_act(C, E, A) :: clock(whenever(C, (next E)), A).
*/