(** * MoreTactics: Advanced uses of [move] and [case]. *)

Require Import ssreflect.
Require Export Logic.

(** This chapter presents sophisticated uses of the two tactics we use
    most: [move] and [case]. *)

(** ** Inversion via [case] *)

(** We have seen so far how to construct proofs for some inductive
    predicate.  For instance, take the [ev] predicate from [Prop.v].
    It characterices the proposition of a number being even by two
    rules:

                          ev n
         ---- (ev_0)  ------------ (ev_SS)
         ev 0         ev (S (S n))

    For instace, here is a proof that 4 is even.
*)

Theorem even4 : ev 4.
Proof.
  do 2!apply: ev_SS.
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


(** Basically, [case] is requiring some help.  We need to provide an
    interpretention for the parameter(s) of the inductive type.  This
    is done via the [/] notation.  To the left of the [/] we say what
    we expect this parameter to be equal to.  To the right, as usual,
    we have the element we are casing on. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  move=>H.
  (* In this case, we want [n] to be equal to [5]. *)
  case P: 5 / H =>[|n En].
  - by []. (* The first case is trivial as before. *)
  (* notice the context, now it has the extra knowledge [P] that [S (S
  n)] is equal to [5].  If we [case] on [P] we get the hypothesis that
  [3 = n].  We use this hypothesis to rewrite [n] to [3] in [En].  *)
  case: P En=><-.
  (* We can repeat the process.  I'm using [{n}] to clear [n] from the
  context, so I can use the name again.  Note that I don't need to
  move the hiopthesis to the context. *) 
  case P : 3 / {n} =>[|n En].
  - by [].  (* We have an absurd in the context: [3 = 0]. *) 
  case: P En=><-.
  (* Now we have [ev 1].  We repeat the process and now we get two
  absurds easy to knock out [by []].  It is strange, but we can even
  omit giving the argument ([1] in this case), and simple write an
  underscore.  So [case] is asking for help but not really needing
  it... *)
  case P : _ / {n} =>[|n En].
  - by [].
  by []. (* Another absurd in the hypothesis. *)
Qed.


(** **** Exercise: 1 star (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem five_not_even :  
  ~ ev 5.
Proof. 
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 1 star (ev_not_ev_S) *)
(** Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  rewrite /not => n H.
  elim: H. (* not n! *)
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star (no_nostutter) *)
(** Remember the example from the file [Prop.v].  Now you should be able to build the proof. *)
Example test_nostutter_4:      ~ (nostutter [:: 3;1;1;4]).
(* FILL IN HERE *) Admitted.
(** [] *)


(** It seems like a lot of work for proving something as easy as "if 5
    is even, then 2+2 = 9".  As a matter of fact, Coq includes a
    tactic called [inversion] that performs this kind of analysis,
    without requiring hints from the user.  The problem with this
    tactic is that it is obscure, slow, and it generates extremely
    large proof terms.

    In the next section we will see an alternative to inversion.
*)

(** ** Proof by computation and the [move/] tactic *)
(**
    In many cases it's not even necessary to conduct this kind of
    proofs.  For instance, in the case of [ev], we have another way of
    proving this nonesense: use the boolean predicate [evenb].  
    We saw in [Prop.v] that from a [ev n] we can get [evenb n = true]:  *)

Check ev__evenb.

(** In a case where we have both a predicate (in [Prop]) and a
    boolean predicate, we can use computation instead of inversion. *)
Theorem even5_nonsense_simple : 
  ev 5 -> 2 + 2 = 9.
Proof.
  move=>H.
  move: (ev__evenb _ H).  (* we get [evenb 5] as hypothesis, which reduces to [false] *)
  by [].                  (* therefore, we have an absurd in our hypothesis, we conclude *)
Qed.

(** Here is another example, where we also use [evenb__ev]. *)
Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  move=>n H.
  move: {H} (ev__evenb _ H). (* we get [evenb (S (S n))]. 
                                ({H} erases the hypothesis H.) *)
  rewrite /=.                (* [evenb (S (S n))] reduces to [evenb n] *)
  move=> H. 
  by apply: evenb__ev.
Qed.


(** In the example above we have to first move the hypothesis to the
    context, and then use it with the theorem [ev__evenb].
    Conveniently, Ssreflect has a way of avoid this pop to the
    context, push to the goal as an argument of a lemma.  This is done
    with the [move/] tactic.  
*)
Theorem SSev__even_short n :
  ev (S (S n)) -> ev n.
Proof.
  move/ev__evenb. 
  rewrite /=.
  move/evenb__ev.
  by [].
Qed.


(** **** Exercise: 1 star (ev_computation) *)
(** Redo the following examples using computation *)
Theorem SSSSev__even_comp n :
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem five_not_even_comp :  
  ~ ev 5.
Proof. 
  (* FILL IN HERE *) Admitted.
 


(** **** Exercise: 3 stars, advanced (ev_ev__ev) *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus) *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


