(** * Induction: Proof by Induction *)

Require Import ssreflect.

(** The next line imports all of our definitions from the
    previous chapter. *)
Require Export Basics.

(** For it to work, you need to use [coqc] to compile [Basics.v]
    into [Basics.vo].  (This is like making a .class file from a .java
    file, or a .o file from a .c file.)
  
    Here are two ways to compile your code:
  
     - CoqIDE:
   
         Open [Basics.v].
         In the "Compile" menu, click on "Compile Buffer".
   
     - Command line:
   
         Run [coqc Basics.v]

    *)

(* ###################################################################### *)
(** * Cases discipline *)

(** There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit identation symbols
    ([-],[+],[*]) placed at the beginning of each case, and each case
    is finished with the [by] tactical, then the proof structure will
    be readable almost no matter what choices are made about other
    aspects of layout.  In the Ssreflect style, the last case is not
    indented, but ultimately this is your own choice.

    This is a good place to mention one other piece of (possibly
    obvious) advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or entire proofs on one line.  Good style lies somewhere in the
    middle.  In particular, one reasonable convention is to limit
    yourself to 80-character lines.  Lines longer than this are hard
    to read and can be inconvenient to display and print.  Many
    editors have features that help enforce this.

    Also, we should mention one key characteristic of Ssreflect:
    conciseness.  Ssreflect is optimized to do several operations at
    once, shortening considerably the size of the script.
 *)

(** The following example presents subcases marking: *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  move=> b c.
  case: b=> H.
  - by [].  (* <----- first case *)
  by []. (* <----- last case *)
Qed.

(** Notice the use of [case]. Since we need to perform a case analysis
on the first variable, we first introduce the two variables, and then
we "bring back" variable [b] with the [:] tactical.  The code above
can also be written in the following way (try it!):
[
  move=> b c.
  move: b.
  case=> H.
  - by [].
  by [].
]
*)

(** **** Exercise: 2 stars (andb_true_elim2) *)
(** Prove [andb_true_elim2], marking cases (and subcases) when
    you use [case]. *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################################### *)
(** * Proof by Induction *)

(** We proved in the last chapter that [0] is a neutral element
    for [+] on the left using a simple argument.  The fact that it is
    also a neutral element on the _right_... *)

Theorem addn0_firsttry : forall n:nat,
  n + 0 = n.

(** ... cannot be proved in the same simple way.  Just applying
  [reflexivity] doesn't work: the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  move=> n.
  rewrite /=. (* Does nothing! *)
Abort.

(** And reasoning by cases using [case] doesn't get us much
   further: the branch of the case analysis where we assume [n = 0]
   goes through, but in the branch where [n = S n'] for some [n'] we
   get stuck in exactly the same way.  We could use [case] again to
   get one step further, but since [n] can be arbitrarily large, if we
   try to keep on like this we'll never be done. *)

Theorem addn0_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  case=>[| n'].
  - by []. (* so far so good... *)
  rewrite /=.       (* ...but here we are stuck again *)
Abort.

(** To prove such facts -- indeed, to prove most interesting
    facts about numbers, lists, and other inductively defined sets --
    we need a more powerful reasoning principle: _induction_.

    Recall (from high school) the principle of induction over natural
    numbers: If [P(n)] is some proposition involving a natural number
    [n] and we want to show that P holds for _all_ numbers [n], we can
    reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same but the order is backwards: we
    begin with the goal of proving [P(n)] for all [n] and break it
    down (by applying the [elim] tactic) into two separate
    subgoals: first showing [P(O)] and then showing [P(n') -> P(S
    n')].  Here's how this works for the theorem we are trying to
    prove at the moment: *)

Theorem addn0 : forall n:nat, n + 0 = n.
Proof.
  elim=> [| n'].
  - by [].
  by move=> /= ->. 
Qed.

(** Like with [case] and [move], we compose the [elim] tactic with
    tactical[=>...]  that specifies the names of the variables to be
    introduced in the subgoals.  In the first branch, [n] is replaced
    by [0] and the goal becomes [0 + 0 = 0], which follows by
    simplification.  In the second, [n] is replaced by [S n'] and the
    assumption [n' + 0 = n'] is added to the goal.  The goal in this
    case becomes then [n' + 0 = n' -> (S n') + 0 = S n'], which
    simplifies to [S (n' + 0) = S n'], which in turn follows from the
    induction hypothesis.  This is solved in Ssreflect with the one
    line [by move=> /= ->].  We saw the _item_ [/=] before, it means
    "simplify", and we use it with the [rewrite] tactic, but it can
    actually be used in many contexts, as we see here.  So [move=> /=]
    does exactly the same as [rewrite /=], although we can next use
    the [->] _pattern_ to perform a rewrite of the first hypothesis in
    the goal.  Putting the pieces together, [move=> /= ->] first
    simplify the goal and then rewrites the inductive hypothesis in
    the goal, getting the result [S n' = S n'], which is in turn
    killed with the [by] tactical. *)

Theorem subnn : forall n,
  minus n n = 0.
Proof.
  elim=>[|n' /= ->].
  - by [].
  by [].
Qed.

(** **** Exercise: 2 stars (basic_induction) *)

(** Prove the following lemmas using induction. You might need
    previously proven results. *)

Theorem muln0 : forall n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem addSadd : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  (* FILL IN HERE *) Admitted.


Theorem addnC : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.


Theorem addnA : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars (double_plus) *)

(** Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_addn : forall n, double n = n + n .
Proof.  
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** Exercise: 1 star (case_elim) *)
(** Briefly explain the difference between the tactics
    [case] and [elim].  

(* FILL IN HERE *)

*)
(** [] *)


(* ###################################################################### *)
(** * Proofs Within Proofs *)


(** In Coq, as in informal mathematics, large proofs are very often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  Occasionally, however, a proof will need some
    miscellaneous fact that is too trivial (and of too little general
    interest) to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    [have] tactic allows us to do this.  For example, our earlier
    proof of the [muln_add0n] theorem referred to a previous theorem
    named [add0n].  We can also use [have] to state and prove [add0n]
    in-line: *)

Theorem muln_add0n' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  move=> n m.
  have: 0 + n = n. 
  - by [].
  move=>->.
  by [].
Qed.

(** The [have] tactic introduces two sub-goals.  The first is the
    assertion itself.  The second goal is the same as the one at the
    point where we invoke [have], except that, as hypothesis, we have
    the assumption that [0 + n = n].  That is, [have] generates
    one subgoal where we must prove the asserted fact and a second
    subgoal where we can use the asserted fact to make progress on
    whatever we were trying to prove in the first place. *)

(** Actually, [have] will turn out to be handy in many sorts of
    situations.  For example, suppose we want to prove that [(n + m)
    + (p + q) = (m + n) + (p + q)]. The only difference between the
    two sides of the [=] is that the arguments [m] and [n] to the
    first inner [+] are swapped, so it seems we should be able to
    use the commutativity of addition ([addnC]) to rewrite one
    into the other.  However, the [rewrite] tactic is a little stupid
    about _where_ it applies the rewrite.  There are three uses of
    [+] here, and it turns out that doing [rewrite addnC]
    will affect only the _outer_ one. *)

Theorem addn_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  move=> n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like addnC should do the trick! *)
  rewrite addnC.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Abort.

(** To get [addnC] to apply at the point where we want it, we can
    introduce a local lemma stating that [n + m = m + n] (for
    the particular [m] and [n] that we are talking about here), prove
    this lemma using [addnC], and then use this lemma to do the
    desired rewrite. *)

Theorem addn_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  move=> n m p q.
  have: n + m = m + n.
    by rewrite addnC.
  move=> ->. 
  by []. 
Qed.

(** But, actually, Ssreflect is equipped with a smart [rewrite]
    tactic, where we can specify precisely which part of the term to
    rewrite.  This is specified between brackets: *)

Theorem addn_rearrange' : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  move=> n m p q.
  rewrite [n + m]addnC.
  by [].
Qed.

(** Even more, we can use a _pattern_, containing an open term. Notice
    the underscore [_] in the pattern. *)

Theorem addn_rearrange'' : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  move=> n m p q.
  rewrite [n + _]addnC.
  by [].
Qed.

(** **** Exercise: 4 stars (mulnC) *)
(** Use [have] to help prove this theorem.  You shouldn't need to
    use induction. *)
Theorem addnCA : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now prove it again, but this time using patterns *)
Theorem addnCA' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.)  You may find that [addnCA] comes in
    handy. *)

Theorem mulnC : forall m n : nat,
 m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (evenb_n__oddb_Sn) *)

(** Prove the following simple fact: *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ###################################################################### *)
(** * More Exercises *)

(** **** Exercise: 3 stars, optional (more_exercises) *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before hacking!) *)

Theorem leqnn : forall n:nat,
  leq n n = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_eqn_S : forall n:nat,
  eqn 0 (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem addn_leq_compat_l : forall n m p : nat, 
  leq n m = true -> leq (p + n) (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_eqn_0 : forall n:nat,
  eqn (S n) 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mul1n : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem addnl : forall n m p, m = p -> n + m = n + p.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem muln_addn_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem muln_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (eqnn) *)
(** Prove the following theorem. *)

Theorem eqnn : forall n : nat, 
  eqn n n = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** Exercise: 3 stars (binary_commute) *)
(** Recall the [increment] and [binary-to-unary] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that these functions commute -- that is, incrementing a binary
    number and then converting it to unary yields the same result as
    first converting it to unary and then incrementing.

    (Before you start working on this exercise, please copy the
    definitions from your solution to the [binary] exercise here so
    that this file can be graded on its own.  If you find yourself
    wanting to change your original definitions to make the property
    easier to prove, feel free to do so.) *)

(* FILL IN HERE *)
(** [] *)


(** **** Exercise: 5 stars, advanced (binary_inverse) *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    the previous exercise to complete this one.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, it is not true!
        Explain what the problem is.

    (c) Define a function [normalize] from binary numbers to binary
        numbers such that for any binary number b, converting to a
        natural and then back to binary yields [(normalize b)].  Prove
        it.

    Again, feel free to change your earlier definitions if this helps
    here. 
*)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(** * Advanced Material *)

(** ** Formal vs. Informal Proof *)

(** "Informal proofs are algorithms; formal proofs are code." *)

(** The question of what, exactly, constitutes a "proof" of a
    mathematical claim has challenged philosophers for millenia.  A
    rough and ready definition, though, could be this: a proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true.
    That is, a proof is an act of communication.

    Now, acts of communication may involve different sorts of readers.
    On one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is a simple mechanical check that
    [P] can be derived from a certain set of formal logical rules, and
    the proof is a recipe that guides the program in performing this
    check.  Such recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    thus necessarily _informal_.  Here, the criteria for success are
    less clearly specified.  A "good" proof is one that makes the
    reader believe [P].  But the same proof may be read by many
    different readers, some of whom may be convinced by a particular
    way of phrasing the argument, while others may not be.  One reader
    may be particularly pedantic, inexperienced, or just plain
    thick-headed; the only way to convince them will be to make the
    argument in painstaking detail.  But another reader, more familiar
    in the area, may find all this detail so overwhelming that they
    lose the overall thread.  All they want is to be told the main
    ideas, because it is easier to fill in the details for themselves.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.  In practice, however,
    mathematicians have developed a rich set of conventions and idioms
    for writing about complex mathematical objects that, within a
    certain community, make communication fairly reliable.  The
    conventions of this stylized form of communication give a fairly
    clear standard for judging proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can ignore
    the informal ones!  Formal proofs are useful in many ways, but
    they are _not_ very efficient ways of communicating ideas between
    human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem addnA' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. move=> n m p. by elim: n => [| n' /= ->].  Qed.

(** Coq is perfectly happy with this as a proof.  For a human,
    however, it is difficult to make much sense of it.  If you're used
    to Coq and Ssreflect you can probably step through the tactics one
    after the other in your mind and imagine the state of the context
    and goal stack at each point, but if the proof were even a little
    bit more complicated this would be next to impossible.  Instead, a
    mathematician might write it something like this: *) 
(** -
    _Theorem_: For any [n], [m] and [p], n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show 
        0 + (m + p) = (0 + m) + p.  
      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where
        n' + (m + p) = (n' + m) + p.
      We must show
        (S n') + (m + p) = ((S n') + m) + p.
      By the definition of [+], this follows from
        S (n' + (m + p)) = S ((n' + m) + p),
      which is immediate from the induction hypothesis. [] *)

(** The overall form of the proof is basically similar.  This is
    no accident: Coq has been designed so that its [elim] tactic
    generates the same sub-goals, in the same order, as the bullet
    points that a mathematician would write.  But there are
    significant differences of detail: the formal proof is much more
    explicit in some ways (e.g., the use of [/=] or [//]) but much
    less explicit in others (in particular, the "proof state" at any
    given point in the Coq proof is completely implicit, whereas the
    informal proof reminds the reader several times where things
    stand). *)

(** Here is a formal proof that shows the structure more
    clearly: *)

Theorem addnA'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  move=> n m p. elim: n => [| n' IH]. 
  - by []. (* Base case *) 
  rewrite /=. rewrite IH. by [].
Qed.

(** Ultimately, what one needs to think when writing a proof is "what
    do I need to communicate about my proof?", and act
    accordingly. Some one-liner proofs like the one above are
    perfectly understandable at the high level: it's performing
    induction on [n]. Do we care about the details in this case?
    Probably not. And this is the philosophy behind Ssreflect: the
    details should be hiden as much as possible, and they should not
    stand on our way. It is only the structure of the proof that
    matters.

    To give an idea, the theorem [addnA'] in plain Coq is way more
    verbose, even if we try to be as concise as possible:
*)

Theorem addnA'_in_plain_coq : forall n m p : nat,
   n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n']. reflexivity. 
  simpl. rewrite -> IHn'. reflexivity.  
Qed.


(** **** Exercise: 2 stars, advanced (addnC_informal) *)
(** Translate your solution for [addnC] into an informal proof. *)

(** Theorem: Addition is commutative.
 
    Proof: (* FILL IN HERE *)
[]
*)

(** **** Exercise: 2 stars, optional (eqnn_informal) *)
(** Write an informal proof of the following theorem, using the
    informal proof of [addnA] as a model.  Don't just
    paraphrase the Coq tactics into English!
 
    Theorem: [eqnn n n] for any [n].
    
    Proof: (* FILL IN HERE *)
[]
 *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)
