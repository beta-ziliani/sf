(** * MoreTactics: Advanced tactics *)

Require Import ssreflect.
Require Export Logic.

(** This chapter presents sophisticated uses of the tactics we've
    seen already, and some new tactics like [pose] and [set]. *)

(** ** Inversion *)

(** We have seen so far how to construct proofs for some inductive
    predicate.  For instance, take the [ev] predicate from [Prop.v].  It characterices the proposition of a number being even by two rules:

                          ev n
         ---- (ev_0)  ------------ (ev_SS)
         ev 0         ev (S (S n))

For instace, here is a proof that 4 is even.
*)

Theorem even4 : ev 4.
Proof.
  apply: ev_SS.
  apply: ev_SS.
  by apply: ev_0.
Qed.

(** This proof is constructed by "going up" from the conclusions to
    the premises.  To prove that a number [m] greater or equal than
    two is even, it suffices to prove that the number [m-2] is even,
    and so on until we reach [0]. *)

(** Now, can we get information the other way around?  That is, from a
    hypothesis that a certain number is even, can we draw a conclusion
    about it?  This is what inversion is about: to use the rules in
    the opposite direction.  

    We saw this already.  The [case] tactic allowed us to consider
    each option for the hypothesis [ev n] in the example [ev_minus2]: *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  move=> n. case.
  - by apply: ev_0.
  move=> n' H /=.
  by [].
Qed.


(** But if we look closely at the previous proof, there is no
    connection between [n], the parameter of the inductive type [ev],
    and the cases.  That is, we don't know that in the first case [n]
    should be [0] and in the second case [n] should be [S (S n')].  In
    this example we did not need this information, but usually we will
    need that the [case] tactic draw this kind of conclusions. *)


(** Consider the following example, where we want to conclude a
    falsity via some absurd hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  case.
  - by [].
  move=> n.
  (* Now we have the hypothesis that [n] is even, it is not anymore an absurd! *)
Abort.

(** Remember when we used a name to create the equation for the different cases: *)
Theorem silly : forall n, if n == 3 is true then 3 == n else ~~ (3 == n).
Proof.
  move=>n.
  case H : (n == 3).
  - by rewrite eqnC.
  by rewrite eqnC H.
Qed.

(** We can try to give a name to [case], in order to get an equation.
    However this will not work, since in the inductive case [ev_SS] it
    has to equate [ev n] to [ev 5], which is false. *)
Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  move=> H.
  Fail case H' : H.
  (* Error: Illegal application (Type Error): 
   The term "eq" of type "forall A : Type, A -> A -> Prop"
   cannot be applied to the terms
    "ev 5" : "Prop"
    "H" : "ev 5"
    "e" : "ev n"
   The 3rd term has type "ev n" which should be coercible to 
   "ev 5". *)
Abort.


(** Basically, Coq is asking us for some help.  We need to provide him
with a way of in terpreting the parameter for the inductive type.  *)
Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  move=>H.
  case P: _ / H =>[|n En].
  - by [].
  (* notice the context, now it has the extra knowledge [P] that [S (S
  n)] is equal to [5].  If we [case] on [P] we get the hypothesis that
  [3 = n].  We use this hypothesis to rewrite [n] to [3] in [En].  *)
  case: P En=><-.
  (* We can repeat the process.  I've used [{n}] to clear [n] from the
  context, so I can use the name again. *) 
  case P : _ / {n} =>[|n En].
  - by [].  (* Notice that we have an absurd in the context: [3 = 0]. *)
  case: P En=><-.
  (* Now we have [ev 1].  We repeat the process and now we get two
  absurds easy to knock out [by []]. *)
  case P : _ / {n} =>[|n En].  
  - by [].
  by [].
Qed.


(** It seems like a lot of work for proving somethig as easy as *)