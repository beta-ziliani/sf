(** * Prop: Propositions and Evidence *)

Require Import ssreflect.
Require Export MoreCoq.

(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions 
    ([forall x, P]).  

    This chapter will take us on a first tour of the
    propositional (logical) side of Coq.
    In particular, we will expand our repertoire of primitive
    propositions to include _user-defined_ propositions, not just
    equality propositions (which are more-or-less "built in" to Coq). 
*)


(* ##################################################### *)
(** * Inductively Defined Propositions *)

(**  As a running example, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.  

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion hold unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   

    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:

         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty) *)
(** How many different ways are there to show that [8] is [beautiful]? *)

(* FILL IN HERE *)
(** [] *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).


(** The first line declares that [beautiful] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    [beautiful]" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  Each of the remaining lines
    embodies one of the rules for [beautiful] numbers.

    The rules introduced this way have the same status as proven 
    theorems; that is, they are true axiomatically. 
    So we can use Coq's [apply:] tactic with the rule names to prove 
    that particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the rule [b_3]. *)
   by apply: b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply: (b_sum 3 5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have rules for both. *)
   - by apply: b_3.
   by apply: b_5.
Qed.

(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  move=> n B.
  apply: b_sum.
  - by apply: eight_is_beautiful.
  by apply: B.
Qed.
  

(** **** Exercise: 2 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(** ** Induction Over Evidence *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    two constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]), 
      - [E] is [b_5] (and [n] is [5]), or 
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)
    
(** This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [elim] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree) *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.
 
(* FILL IN HERE *)
[]
*)


(** **** Exercise: 1 star (gorgeous_plus13) *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
   (* FILL IN HERE *) Admitted.
(** [] *)

(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
  move=>n.
  elim=> [|n' G B|n' G B].
  - by apply: b_0.
  - apply: b_sum. 
    + by apply: b_3.
    by []. 
  apply: b_sum. 
  - by apply: b_5.
  apply B. 
Qed.

(** Notice that the argument proceeds by induction on the _evidence_ [H]! *) 

(** Let's see what happens if we try to prove this by induction on [n]
   instead of induction on the evidence [H]. *)

Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   elim=>[|n' IH] G.
   - by apply: b_0.
   (* We are stuck! *)
Abort.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)




(** **** Exercise: 2 stars (gorgeous_sum) *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous) *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (g_times2) *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
   (* FILL IN HERE *) Admitted.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   move=> n H /=. 
   elim: H.
   (* FILL IN HERE *)  Admitted.
(** [] *)


(* ####################################################### *)
(** ** From Boolean Functions to Propositions *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even by using the coercion presented in [MoreCoq]. *)

(** That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."  
*)

(** Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** This definition says that there are two ways to give
    evidence that a number [m] is even.  First, [0] is even, and
    [ev_0] is evidence for this.  Second, if [m = S (S n)] for some
    [n] and we can give evidence [e] that [n] is even, then [m] is
    also even, and [ev_SS n e] is the evidence. *)


(** **** Exercise: 1 star (double_even) *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** *** Discussion: Computational vs. Inductive Definitions *)

(** We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  

    The advantage of the function [evenb] is that it gives us many
    theorems for free.  Indeed, while the proposition "[6] is even"
    requires [3] applications of [ev_SS] and one of [ev_0], it is
    trivial to see that [evenb 6] returns [true].  In the exercises we
    saw already the convenience of this formulation, where we never
    cared to show that [evenb (S (S n))] is equal to [evenb n], for
    any [n].

    However, there are properties of interest in which the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)




(** **** Exercise: 1 star (ev__even) *)
(** Here is a proof that the inductive definition of evenness implies
    the computational one. *)

Theorem ev__evenb : forall n,
  ev n -> evenb n.
Proof.
  move=> n. elim=> [| n' E' IH].
  - by [].
  by apply: IH.  
Qed.

(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* FILL IN HERE *)
(** [] *)



(** The induction principle for inductively defined propositions does
    not follow quite the same form as that of inductively defined
    sets.  For now, you can take the intuitive view that induction on
    evidence [ev n] is similar to induction on [n], but restricts our
    attention to only those numbers for which evidence [ev n] could be
    generated.  We'll look at the induction principle of [ev] in more
    depth below, to explain what's really going on. *)

(** **** Exercise: 1 star (l_fails) *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       elim=> [|n' IH].
       - by apply: ev_0.
       ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?

(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars (ev_sum) *)
(** Here's another exercise requiring induction. *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ####################################################### *)
(** ** [case] on Evidence *)

(** Another situation where we want to analyze evidence for evenness
    is when proving that, if [n] is even, then [pred (pred n))] is
    too.  In this case, we don't need to do an inductive proof.  The
    right tactic turns out to be [case].  *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  move=> n. case.
  - by apply: ev_0.
  move=> n' H /=.
  by [].
Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n) *)
(** What happens if we try to use [case] on [n] instead of on [E]? *)

(* FILL IN HERE *)
(** [] *)



(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars (palindromes) *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
    c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove that 
       forall l, pal (l ++ rev l).
*)

(* FILL IN HERE *)
(** [] *)


(** **** Exercise: 2 stars, optional (R_provability) *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 [::]
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [:: 1; 0]]
    - [R 1 [:: 1; 2; 1; 0]]
    - [R 6 [: 3; 2; 1; 0]]
*)

(** [] *)






(* ##################################################### *)
(** * Programming with Propositions *)

(** A _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop].  Although we haven't discussed this
    explicitly, we have already seen numerous examples. *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (3 == 2 = false).
(* ===> (3 == 2) = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. by [].  Qed.

(** But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. by [].  Qed.

(** We've seen several ways of constructing propositions.  

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)

(** We have also seen _parameterized propositions_, such as [beautiful]. *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)
Check (beautiful 8).
(* ===> beautiful 8 : Prop *)
Check beautiful. 
(* ===> beautiful : nat -> Prop *)

(** The type of [beautiful], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[beautiful] is a _function_ from numbers to
    propositions," (2) "[beautiful] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[beautiful] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)

Definition between (n m o: nat) : Prop :=
  (n <= o) && (o <= m).

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** Here are two more examples of passing parameterized propositions
    as arguments to a function.  

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 



(** **** Exercise: 3 stars (combine_odd_even) *)
(** Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  (* FILL IN HERE *) admit.

(** To test your definition, see whether you can prove the following
    facts: *)

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere) *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)
(*
Fixpoint true_upto_n__true_everywhere n P :=
(* FILL IN HERE *)

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => evenb n))
  = (evenb 3 -> evenb 2 -> evenb 1 -> forall m : nat, evenb m).
Proof. by [].  Qed.
*)
(** [] *)













(** Power of computation.   MOVE THIS TO MoreProp? *)

  
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




(* $Date: 2013-07-01 18:48:47 -0400 (Mon, 01 Jul 2013) $ *)


