(** * MoreCoq: More About Coq *)

Require Import ssreflect.
Require Export Poly.

(** This chapter introduces several more Coq tactics that,
    together, allow us to prove many more theorems about the
    functional programs we are writing. *)

(* ###################################################### *)
(** * The [apply:] Tactic *)

(** We often encounter situations where the goal to be proved is
    exactly the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [:: n;o] = [:: n;p] ->
     [:: n;o] = [:: m;p].
Proof.
  move=> n m o p eq1 eq2.
  rewrite -eq1.
  (* At this point, we could finish with 
     "[by rewrite eq2.]" as we have 
     done several times above. But we can achieve the
     same effect in a single step by using the 
     [apply:] tactic instead: *)
  by apply: eq2.  
Qed.

(** The [apply:] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [:: q;o] = [:: r;p]) ->
     [:: n;o] = [:: m;p].
Proof.
  move=> n m o p eq1 eq2. 
  apply: eq2. 
  by apply: eq1.  
Qed.

(** You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply:]. *)

(** Typically, when we use [apply: H], the statement [H] will
    begin with a [forall] binding some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply: eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [:: q] = [:: r]) ->
     [:: n] = [:: m].
Proof.
  move=> n m eq1 eq2.
  apply: eq2. 
  by apply: eq1. 
Qed.

(** **** Exercise: 2 stars, optional (silly_ex) *)
(** Complete the following proof without using [rewrite /=]. *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** To use the [apply:] tactic, the (conclusion of the) fact
    being applied must match the goal _exactly_ -- for example, [apply:]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = eqn n 5  ->
     eqn (S (S n)) 7 = true.
Proof.
  move=> n H.
  rewrite /=.
  (* Here we cannot use [apply:] directly *)
Abort.

(** In this case we can use the [symmetry] tactic, which switches the
    left and right sides of an equality in the goal. *)

Theorem silly3 : forall (n : nat),
     true = eqn n 5  ->
     eqn (S (S n)) 7 = true.
Proof.
  move=> n H.
  symmetry.
  rewrite /=. (* Actually, this [rewrite /=] is unnecessary, since 
            [apply:] will try reducing the goal. *)  
  by apply: H.
Qed.

(** **** Exercise: 3 stars (apply_exercise1) *)
(** Hint: you can use [apply:] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [Search] is
    your friend. *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, optional (apply_rewrite) *)
(** Briefly explain the difference between the tactics [apply:] and
    [rewrite].  Are there situations where both can usefully be
    applied?
  (* FILL IN HERE *)
*)
(** [] *)


(* ###################################################### *)
(** * The [apply:] Tactic with Arguments *)

(** The following silly example uses two rewrites in a row to
    get from [[:: a,b]] to [[:: e,f]]. *)

Example eq_trans_example : forall (a b c d e f : nat),
     [:: a;b] = [:: c;d] ->
     [:: c;d] = [:: e;f] ->
     [:: a;b] = [:: e;f].
Proof.
  move=> a b c d e f eq1 eq2. 
  rewrite eq1. rewrite eq2.
  by []. 
Qed.

(** Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)

Theorem eq_trans : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof. by move=> X n m o -> ->. Qed.

(** Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply:] tactic. *)

Example eq_trans_example' : forall (a b c d e f : nat),
     [:: a;b] = [:: c;d] ->
     [:: c;d] = [:: e;f] ->
     [:: a;b] = [:: e;f].
Proof.
  move=> a b c d e f eq1 eq2. 
  (* If we simply tell Coq [apply: eq_trans] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [[nat]], [n] with [[:: a,b]], and [o] with [[::e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [[:: c,d]] as the third argument to the invocation of
     [apply:]. *)
  apply: (eq_trans _ _ [:: c;d]). 
  apply: eq1. 
  by apply: eq2.   
Qed.

(** **** Exercise: 3 stars, optional (apply_with_exercise) *)
Example eq_trans_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(** * The [case] tactic for injection *)

(** Recall the definition of natural numbers:
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
    It is clear from this definition that every number has one of two
    forms: either it is the constructor [O] or it is built by applying
    the constructor [S] to another number.  But there is more here than
    meets the eye: implicit in the definition (and in our informal
    understanding of how datatype declarations work in other
    programming languages) are two other facts:

    - The constructor [S] is _injective_.  That is, the only way we can
      have [S n = S m] is if [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)

(** Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor is
    injective and [nil] is different from every non-empty list.  For
    booleans, [true] and [false] are unequal.  (Since neither [true]
    nor [false] take any arguments, their injectivity is not an issue.) *)

(** Coq/Ssreflect provides tactic [case] and tactical [by] with the
    ability to exploit these principles in proofs.
 
    The [case] tactic is used like this.  Suppose [H] is a
    hypothesis in the context (or a previously proven lemma) of the
    form
      c a1 a2 ... an = c b1 b2 ... bm
    for some constructor [c] and arguments [a1 ... an] and
    [b1 ... bm].  Then [case: H] (or simply [case] if the goal is of
    the form [H -> G]) instructs Coq to "inject" this equality to
    extract the information it contains about these terms: by the
    injectivity of this constructor we know that [a1 = b1], [a2 = b2],
    etc.; [case: H] adds these facts to the goal as [a1 = b1 -> a2 = b2 -> ...].

    If, instead, we have a hypothesis [H] of the form 
      c a1 a2 ... an = d b1 b2 ... bm 
    for some constructor [c] and [d], and arguments [a1 ... an]
    and [b1 ... bm], where [c] and [d] are different constructors,
    then the hypothesis [H] is contradictory.  That is, a false
    assumption has crept into the context, and this means that any
    goal whatsoever is provable!  In this case, [by] marks
    the current goal as completed and pops it off the goal stack. *)

(** These particular usages of [case] and [by] is probably easier to understand by
    seeing them in action than from general descriptions like the above.
    Below you will find example theorems that demonstrate the use of
    [case] and [by], and exercises to test your understanding. *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  move=> n m. 
  case. 
  by [].
Qed.

Theorem silly4 : forall (n m : nat),
     [:: n] = [:: m] ->
     n = m.
Proof.
  move=> n o.
  by case. 
Qed.

(** As a convenience, the [case] tactic can also
    destruct equalities between complex values, binding
    multiple variables as it goes. *)

Theorem silly5 : forall (n m o : nat),
     [:: n;m] = [:: o;o] ->
     [:: n] = [:: m].
Proof.
  move=> n m o.
  case. 
  by move=>->->. 
Qed.

(** **** Exercise: 1 star (sillyex1) *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  move=>n. by [].
Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [:: n] = [:: m].
Proof.
  move=> n m.
  by [].
Qed.

(** **** Exercise: 1 star (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [::] ->
     y :: l = z :: j ->
     x = z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** While the injectivity of constructors allows us to reason
    [forall (n m : nat), S n = S m -> n = m], the reverse direction of
    the implication is an instance of a more general fact about
    constructors and functions, which we will often find useful: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A), 
    x = y -> f x = f y. 
Proof. by move=> A B f x y ->.  Qed. 

(** Here's another illustration of [case].  This is a slightly
    roundabout way of stating a fact that we have already proved
    above.  The extra equalities force us to do a little more
    equational reasoning and exercise some of the tactics we've seen
    recently. *)

Theorem size_rcons' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     size l = n ->
     size (rcons l v) = S n. 
Proof.
  move=> X v.
  elim=> [| v' l' IH] n eq.
  - by rewrite -eq.
  rewrite /=. 
  case: n => [|n'] in eq *.
  - by [].
  apply: f_equal. 
  apply: IH.
  case: eq.  (** Note that no simplification was needed! *) 
  by [].
Qed.

(** Note also the use of [in eq *].  It is instructing [case] to push
    the hypothesis [eq] to the goal, do the case on [n], and then pop
    back the hypothesis with the same name, [eq].  More precisely, the
    following sequence of events is triggered by the line
       [case: n => [|n'] in eq *]

    1- [in eq *] pushes [eq] onto the goal, getting
      [ size (v' :: l') = n -> S (size (rcons l' v)) = S n ]

    2-a [case: n] further pushes variable [n] onto the context:
      [ forall n, size (v' :: l') = n -> S (size (rcons l' v)) = S n ]

    2-b [case: n] after pushing [n] performs a case analysis on the
    first hypothesis ([n] in this case), getting subcases

      [ size (v' :: l) = 0 -> S (size (rcons l' v)) = S 0 ]

    and

      [ forall n', size (v' :: l) = n' -> S (size (rcons l' v)) = S n' ]

    3- The tactical for introduction [=>] pops variable [n'] on the second goal.

    4- [in eq *] restores the context, poping the first hypothesis
    giving it the name [eq].

    Note that if we do not introduce the variables from the case (with
    the [=>] tactical) then the last pop operation might potentially
    introduce a different hypothesis (e.g., [n']) instead of [eq].
    But Ssreflect forbids this, throwing a pretty obsucre error message:

    "tampering with discharged assumptions of "in" tactical".

    Finally, the [*] at the end of [in eq *] is telling Coq that the
    tactic ([case]) should affect the goal. *)

(** **** Exercise: 2 stars, (playing_with_in) *)
(** Try removing the [*] in the [in eq *] part of the proof
    [size_rcons'] removing.  What happened?  Try again removing the
    [eq].  How can you do the same without the [in] tactical?
*)

(** **** Exercise: 2 stars, optional (practice) *)
(** A couple more nontrivial but not-too-complicated proofs to work
    together in class, or for you to work as exercises.  They may
    involve applying lemmas from earlier lectures or homeworks. *)
 

Theorem eqn_0_l : forall n,
   eqn 0 n = true -> n = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem eqn_0_r : forall n,
   eqn n 0 = true -> n = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################### *)
(** * Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, as we saw in the previous examples, 
    we can use the [in] tactical to perform the tactic on certain hypotheses.

    For example, the tactic [rewrite /= in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     eqn (S n) (S m) = b  ->
     eqn n m = b. 
Proof.
  move=> n m b H.
  rewrite /= in H.
  by apply: H.
Qed.


(** (But, as we saw in other examples, we can avoid this simplfication
    in the hypothesis if we perform the simplification in the goal
    prior to popping it in the context.) *)

Theorem S_inj' : forall (n m : nat) (b : bool),
     eqn (S n) (S m) = b  ->
     eqn n m = b. 
Proof.
  move=> n m b /= H.
  by apply: H.
Qed.



(** * Digresion: Coercions *)

(** In order to make our theorems more readable, we can "coerce" any
    proposition of the form [b = true] into writting simply [b].  This
    is done in two steps.  First, we create the function [is_true]
    that given a boolean [b] returns the proposition [b = true]. *)

Definition is_true (b : bool) := b = true.

(** Then, we "coerce" any boolean into a proposition by using [is_true]. *)

Coercion is_true : bool >-> Sortclass.

(** Without going into too much detail, basically it is stating that
    when an element of a [Sortclass] is expected (a [Prop] in our
    case), and a [bool] is given, then Coq should use [is_true] to
    perform the coercion. *)

(** With this coercion we can write the following example. *)
Theorem extremely_silly1 : forall n : nat, eqn n 0 -> eqn n 0.
Proof. by []. Qed.

(** We can improve the readability of the theorem further by using a
    standard notation for decidable equality. *)
Notation "x == y" := (eqn x y)
  (at level 70, no associativity).

Theorem extremely_silly2 : forall n : nat, 
     n == 0 -> S n == 1.
Proof. by []. Qed.



(* ###################################################### *)
(** * Backward vs. forward reasoning *)

(** We mentioned at the beginning of this chapter the tactic [apply:].
    Logically speaking, with [H : F -> G], [apply: H] changes goal [G]
    to [F].  That is, it allows us to go "backwards" from [G] to [F],
    in the hope that [F] is simpler to prove.

    Consider the following example.
*)
Theorem extremely_silly3 : forall n, 
     2 == S (S n) -> 0 == n.
Proof.
  move=>n H.
  apply: S_inj.
  apply: S_inj.
  by apply: H.
Qed.

(** Each [apply:] of the [S_inj] theorem adds a [S]uccessor to each
    side of the equality.  After the second application we have the
    goal matching exactly the hypothesis [H], and therefore we
    conclude by applying [H].

    In a similar way we can proceed on the other direction: take [H]
    and "specialize it" to match the goal.  That is, use [S_inj] to
    remove a [S]uccessor from [H], until we have [H] matching our
    goal.  For this we can use the tactic [move].

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem extremelly_silly3' : forall n,
     2 == S (S n) -> 0 == n.
Proof.
  move=>n H.
  move: {H} (S_inj _ _ _ H)=>H.
  move: {H} (S_inj _ _ _ H)=>H.
  by apply: H.
Qed.

(** What is going on here?  Let's see the same example, but
    decomposing each action. *)
Theorem extremelly_silly3'' : forall n,
     2 == S (S n) -> 0 == n.
Proof.
  move=>n H.
(** At this point we want to bring the knowledge that [S_inj] applied
    with [H] removes a successor from [H].  *)
  move: (S_inj _ _ _  H).
(** But [H] is still there!  We need to remove it in order to pop the
    hypothesis back with the same name. *)
  move: H => _ H.
(** That is, we first bring [H] to the goal, getting the goal
    [2 == S (S n) -> 1 == S n -> 0 == n]
    and then we introduce again the first two hypothesis.  But by
    naming the first one [_] we are effectively throwing it away.
    The same effect can be obtained by adding [{H}].  Therefore, 
    the previous two lines can be compressed to the shorter one:
*)
  move: {H} (S_inj _ _ _ H)=>H.
(** And now we are done.  We actually do not need to specify that
  there is a hypothesis proving our goal.*) 
  by [].
Qed.


(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, Coq tends to favor backward reasoning, but in some
    situations the forward style can be easier to use or to think
    about.  *)

(** **** Exercise: 3 stars (plus_n_n_injective) *)
(** Practice using [have], [in], and [move] as we saw in this
    chapter. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  elim=> [| n' IH].
(** Hint: [plus_Sn_m] may be of help. *)
    (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(** * Varying the Induction Hypothesis *)

(** Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Coq.
    In particular, we need to be careful about which of the
    assumptions we move (using [move]) from the goal to the context
    before invoking the [elim] tactic.  For example, suppose 
    we want to show that the [double] function is injective -- i.e., 
    that it always maps different arguments to different results:  
    Theorem double_injective: forall n m, double n = double m -> n = m. 
    The way we _start_ this proof is a little bit delicate: if we 
    begin it with
      elim.
]] 
    all is well.  But if we begin it with
      move=> n m. elim: n.
    we get stuck in the middle of the inductive case... *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  move=>n m. elim: n => [| n'].
  - by case: m.
  case: m => [|m'] IH eq.
  - by [].
  apply: f_equal.
      (* Here we are stuck.  The induction hypothesis, [IH], does
         not give us [n' = m'] -- there is an extra [S] in the
         way -- so the goal is not provable. *)
Abort.

(** What went wrong? *)

(** The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context -- 
    intuitively, we have told Coq, "Let's consider some particular
    [n] and [m]..." and we now have to prove that, if [double n =
    double m] for _this particular_ [n] and [m], then [n = m].

    The next tactic, [elim: n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove that
    the proposition

      - [P n]  =  "if [double n = double m], then [n = m]"

    holds for all [n] by showing

      - [P O]              

         (i.e., "if [double O = double m] then [O = m]")

      - [P n -> P (S n)]  

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular [m] --
    say, [5].  The statement is then saying that, if we know

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help with proving [R]!  (If we
    tried to prove [R] from [Q], we would say something like "Suppose
    [double (S n) = 10]..." but then we'd be stuck: knowing that
    [double (S n)] is [10] tells us nothing about whether [double n]
    is [10], so [Q] is useless at this point.) *)

(** To summarize: Trying to carry out this proof by induction on [n]
    when [m] is already in the context doesn't work because we are
    trying to prove a relation involving _every_ [n] but just a
    _single_ [m]. *)

(** The good proof of [double_injective] leaves [m] in the goal
    statement at the point where the [elim] tactic is invoked on
    [n]: *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  elim=> [| n'].
  - by case.
  (* Notice that both the goal and the induction
     hypothesis have changed: the goal asks us to prove
     something more general (i.e., to prove the
     statement for _every_ [m]), but the IH is
     correspondingly more flexible, allowing us to
     choose any [m] we like when we apply the IH.  *)
  move=> IH m eq.
  (* Now we choose a particular [m] and introduce the
     assumption that [double n = double m].  Since we
     are doing a case analysis on [n], we need a case
     analysis on [m] to keep the two "in sync." *)
  (* We should have left [m] in the goal and perform [case] directly,
     but since we pop it to the goal, we need to make sure we also
     affect [eq] when doing the case.  This is done with the [in]
     tactical. *) 
  case: m => [| m'] in eq *.
    (* The 0 case is trivial *)
  - by [].
  apply: f_equal. 
  (* At this point, since we are in the second
     branch of the [case: m], the [m'] mentioned
     in the context at this point is actually the
     predecessor of the one we started out talking
     about.  Since we are also in the [S] branch of
     the induction, this is perfect: if we
     instantiate the generic [m] in the IH with the
     [m'] that we are talking about right now (this
     instantiation is performed automatically by
     [apply:]), then [IH] gives us exactly what we
     need to finish the proof. *)
  apply: IH.
  case: eq.
  by [].
Qed.

(** What this teaches us is that we need to be careful about using
    induction to try to prove something too specific: If we're proving
    a property of [n] and [m] by induction on [n], we may need to
    leave [m] generic. *)

(** The proof of this theorem has to be treated similarly: *)
(** **** Exercise: 2 stars (eqnP_r) *)
Theorem eqnP_r : forall n m,
    n == m -> n = m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, advanced (eqnP_r_informal) *)
(** Give a careful informal proof of [eqnP_r], being as explicit
    as possible about quantifiers. *)

(* FILL IN HERE *)
(** [] *)


(** The strategy of doing fewer [move]s before an [elim] doesn't
    always work directly; sometimes a little _rearrangement_ of
    quantified variables is needed.  Suppose, for example, that we
    wanted to prove [double_injective] by induction on [m] instead of
    [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  move=> n. elim => [| m'].
  - by case:n.
  case: n => [|n'].
  - by [].
  move=> IH H.
  apply: f_equal.
  (* Stuck again here, just like before. *)
Abort.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  *)

(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    will work, but it's not nice: We don't want to have to mangle the
    statements of lemmas to fit the needs of a particular strategy for
    proving them -- we want to state them in the most clear and
    natural way. *)

(**  What we can do instead is to first introduce all the
    quantified variables and then _re-generalize_ one or more of
    them, taking them out of the context and putting them back at
    the beginning of the goal.  The [move] tactic
    does this. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  move=>n m. 
  (* [n] and [m] are both in the context *)
  move: n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  elim: m => [| m' IH].
  - by case.
  case => [| n'].
  - by [].
  move=> H; apply: f_equal.
  apply: IH.
  by case: H.
Qed.

(** Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves [n] quantified,
    corresponding to the use of [move:] in our formal
    proof.

_Theorem_: For any nats [n] and [m], if [double n = double m], then
  [n = m].

_Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
  any [n], if [double n = double m] then [n = m].

  - First, suppose [m = 0], and suppose [n] is a number such
    that [double n = double m].  We must show that [n = 0].

    Since [m = 0], by the definition of [double] we have [double n =
    0].  There are two cases to consider for [n].  If [n = 0] we are
    done, since this is what we wanted to show.  Otherwise, if [n = S
    n'] for some [n'], we derive a contradiction: by the definition of
    [double] we would have [double n = S (S (double n'))], but this
    contradicts the assumption that [double n = 0].

  - Otherwise, suppose [m = S m'] and that [n] is again a number such
    that [double n = double m].  We must show that [n = S m'], with
    the induction hypothesis that for every number [s], if [double s =
    double m'] then [s = m'].
 
    By the fact that [m = S m'] and the definition of [double], we
    have [double n = S (S (double m'))].  There are two cases to
    consider for [n].

    If [n = 0], then by definition [double n = 0], a contradiction.
    Thus, we may assume that [n = S n'] for some [n'], and again by
    the definition of [double] we have [S (S (double n')) = S (S
    (double m'))], which implies by double injection on [S] that
    [double n' = double m'].

    Instantiating the induction hypothesis with [n'] thus allows us to
    conclude that [n' = m'], and it follows immediately that [S n' = S
    m'].  Since [S n' = n] and [S m' = m], this is just what we wanted
    to show. [] *)

(** **** Exercise: 3 stars (gen_dep_practice) *)

(** Prove this by induction on [l]. *)

Theorem onth_after_last: forall (n : nat) (X : Type) (l : list X),
     size l = n ->
     onth n l = None.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (onth_after_last_informal) *)
(** Write an informal proof corresponding to your Coq proof
    of [index_after_last]:
 
     _Theorem_: For all sets [X], lists [l : list X], and numbers
      [n], if [length l = n] then [index n l = None].
 
     _Proof_:
     (* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars, optional (generalization_practice_more) *)
(** Prove this by induction on [l]. *)

Theorem size_rcons''' : forall (n : nat) (X : Type) 
                              (v : X) (l : list X),
     size l = n ->
     size (rcons l v) = S n. 
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (size_cat_cons) *)
(** Prove this by induction on [l1], without using [size_cat]. *)
Theorem size_cat_cons : forall (X : Type) (l1 l2 : list X) 
                                  (x : X) (n : nat),
     size (l1 ++ (x :: l2)) = n ->
     S (size (l1 ++ l2)) = n.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, optional (size_cat_twice) *)
(** Prove this by induction on [l], without using size_cat. *)

Theorem size_cat_twice : forall (X:Type) (n:nat) (l:list X),
     size l = n ->
     size (l ++ l) = n + n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(** * Using [case:] on Compound Expressions *)

(** We have seen many examples where the [case:] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [case:].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if n == 3 is true then false
  else if n == 5 is true then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  move=> n. rewrite /sillyfun. 
  case: (n == 3).
  - by [].
  case: (_ == _).
  - by [].
  by [].
Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if n == 3 is true then ... else ...].  Well,
    either [n] is equal to [3] or it isn't, so we use [case:
    n == 3] to let us reason about the two cases. 

    [case] actually supports giving a pattern, like in the second 
    [case: (_ == _)].  Coq will find that we actually mean [case: (n == 5)].

    In general, the [case] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [case: e] generates a subgoal
    in which all occurrences of [e] in the goal
    are replaced by [c]. *)



(** **** Exercise: 1 star (override_shadow) *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (combine_split) *)
(** Complete the proof below *)

Theorem zip_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  zip l1 l2 = l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Sometimes, doing a [case:] will erase information we need to
    complete a proof. *)
(** For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if n == 3 is true then true
  else if n == 5 is true then true
  else false.

(** And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n ->
     oddb n.
Proof.
  move=>n. rewrite /sillyfun1.
  case: (n == 3).
  (* stuck... *)
Abort.

(** We get stuck at this point because the context does not contain
    enough information to prove the goal!  The problem is that [case]
    performed the substitution on the goal, and leave no trace of [n
    == 3 = true].  We need to keep some memory of this expression and
    how it was destructed, because we need to be able to reason that
    since, in this branch of the case analysis, [n == 3 = true],
    it must be that [n = 3], from which it follows that [n] is odd.

    What we would really like is to substitute away all existing
    occurences of [n == 3], but at the same time add an equation to
    the context that records which case we are in.  We can do this by
    naming the case (with whatever name we choose). *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  move=> n. rewrite /sillyfun1.
  case neq3: (n == 3).
  (* Now we have the same state as at the point where we got stuck
    above, except that the context contains an extra equality
    assumption, which is exactly what we need to make progress. *)
    - move: (eqnP_r _ _ neq3).
      move=>->.
      by [].
  (* When we come to the second equality test in the body of the
     function we are reasoning about, we can use [case:] again in the
     same way, allow us to finish the proof. *)
    case neq5: (n == 5). 
    - move: (eqnP_r _ _ neq5).
      move=>->.
      by [].
    by [].
Qed.


(** **** Exercise: 2 stars (case_practice) *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars (override_same) *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ################################################################## *)
(** * Review *)

(** We've now seen a bunch of Coq's fundamental tactics and tacticas.
    We'll introduce a few more as we go along through the coming
    lectures, and later in the course we'll introduce some more
    powerful _automation_ tactics that make Coq do more of the
    low-level work in many cases.  But basically we've got what we
    need to get work done.

    Here are the ones we've seen:

      - [=>]: 
        move hypotheses/variables from goal to context 

      - [:]:
        move hypotheses/variables/complex compounds from the context
        to the goal.

      - [by]:
        finish the proof when
        + it is an equality [e = e],
        + it is equal to some hypothesis,
        + there is a contradiction in the hypothesis (like [false = true]).

      - [in H1 .. Hn *]: 
        apply a tactic but first push H1 .. Hn in the context, and the pops
        them back.

      - [apply:]:
        prove goal using a hypothesis, lemma, or constructor

      - [/=]:
        when used within [=>] or [rewrite], simplifies computations in the goal.

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal. 

      - [symmetry]:
        changes a goal of the form [t=u] into [u=t].

      - [rewrite /D]:
        replace a defined constant [D] by its right-hand side.

      - [case H: e]: 
        case analysis on values of inductively defined
        types, and optionally stores equality [e = constructor args] if [H] is
        specified.

      - [case H: e] when [e] has type [c a1 ... an = c b1 ... bn]:
        for [c] a constructor of some inductive type, it equates each [ai = bi].

      - [elim:]:
        induction on values of inductively defined types.

      - [have H: e]:
        introduce a "local lemma" [e] and (optionally) call it [H].
*)

(* ###################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (eqnC) *)
Theorem eqnC : forall (n m : nat),
  n == m = (m == n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (eqnC_informal) *)
(** Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [n == m = m == n].

   Proof:
   (* FILL IN HERE *)
[]
 *)

(** **** Exercise: 3 stars, optional (eqn_trans) *)
Theorem eqn : forall n m p,
  n == m -> m == p -> n == p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (split_zip) *)
(** We have just proven that for all lists of pairs, [zip] is the
    inverse of [split].  How would you formalize the statement that
    [split] is the inverse of [zip]?

    Complete the definition of [split_zip_statement] below with a
    property that states that [split] is the inverse of
    [zip]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [move] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split] [zip l1 l2 = (l1,l2)] to be true?)  *)

Definition split_combine_statement : Prop :=
(* FILL IN HERE *) admit.

Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.


(** [] *)

(** **** Exercise: 3 stars (override_permute) *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  k2 == k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (filter_exercise) *)
(** This one is a bit challenging.  Pay attention to the form of your IH. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced (forall_exists_challenge) *)
(** Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:
      forallb oddb [:: 1;3;5;7;9] = true

      forallb negb [:: false;false] = true
  
      forallb evenb [:: 0;2;4;5] = false
  
      forallb (eqn 5) [::] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:
      existsb (eqn 5) [:: 0;2;3;6] = false
 
      existsb (andb true) [:: true;true;false] = true
 
      existsb oddb [:: 1;0;0;0;0;3] = true
 
      existsb evenb [::] = false

    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].
 
    Prove that [existsb'] and [existsb] have the same behavior.
*)
(* FILL IN HERE *)
(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)



