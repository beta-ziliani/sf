


Theorem evenb__ev' : forall n,
  (evenb n -> ev n) /\ (evenb (S n) -> ev (S n)).
Proof.
  elim=>[].
  split=>H.
    by apply: ev_0.
    by [].
  move=>n [H1 H2].
  split.
  - by [].
  move=> H. apply: ev_SS.
  apply: H1. by [].
Qed.

Theorem evenb__ev : forall n,
  evenb n -> ev n.
Proof.
  move=>n H. 
  by apply: (proj1 (evenb__ev' _)).
Qed.



Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  move=>n.
  move/ev__evenb.
  rewrite /=.
  by move/evenb__ev.
Qed.




(** These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but 
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)    

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)


(** **** Exercise: 1 star (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *) Admitted.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (ev_ev__ev) *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  move=>n m H.
  
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


Theorem five_not_even :  
  ~ ev 5.
Proof. 
  (* WORKED IN CLASS *)
  rewrite /not.
  move/ev__evenb.
  by [].
Qed.



(** **** Exercise: 1 star (ev_not_ev_S) *)
(** Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  rewrite /not => n H.
  elim: H.  (* not n! *)
  (* FILL IN HERE *) Admitted.
(** [] *)














(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, pal l -> l = rev l.
    and
     forall l, l = rev l -> pal l.
*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (subsequence) *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove that subsequence is reflexive, that is, any list is a
      subsequence of itself.  

    - Prove that for any lists [l1], [l2], and [l3], if [l1] is a
      subsequence of [l2], then [l1] is also a subsequence of [l2 ++
      l3].

    - (Optional, harder) Prove that subsequence is transitive -- that
      is, if [l1] is a subsequence of [l2] and [l2] is a subsequence
      of [l3], then [l1] is a subsequence of [l3].  Hint: choose your
      induction carefully!
*)

(* FILL IN HERE *)
(** [] *)






(* ###################################################### *)
(** * Evidence-carrying booleans. *)

(** So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 

It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [|n'].
    intros m.
    destruct m as [|m'].
      left. reflexivity.
      right. intros contra. inversion contra.
    intros m.
    destruct m as [|m'].
      right. intros contra. inversion contra.
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 

(** Read as a theorem, this says that equality on [nat]s is decidable:
that is, given two [nat] values, we can always produce either 
evidence that they are equal or evidence that they are not.
Read computationally, [eq_nat_dec] takes two [nat] values and returns
a [sumbool] constructed with [left] if they are equal and [right] 
if they are not; this result can be tested with a [match] or, better,
with an [if-then-else], just like a regular [boolean]. 
(Notice that we ended this proof with [Defined] rather than [Qed]. 
The only difference this makes is that the proof becomes _transparent_,
meaning that its definition is available when Coq tries to do reductions,
which is important for the computational interpretation.)

Here's a simple example illustrating the advantages of the [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)


(** **** Exercise: 1 star (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)




(* ####################################################### *)
(** ** Inversion, Again (Advanced) *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,
        
      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)

(** _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be the same!  The [inversion] tactic adds this fact to the
   context.  *)

