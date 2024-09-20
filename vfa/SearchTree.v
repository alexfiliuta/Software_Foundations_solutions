(** * SearchTree: Binary Search Trees *)

(** We have implemented maps twice so far: with lists in
    [Lists], and with higher-order functions in [Maps].
    Those are simple but inefficient implementations: looking up the
    value bound to a given key takes time linear in the number of
    bindings, both in the worst and expected case. *)

(** If the type of keys can be totally ordered -- that is, it supports
    a well-behaved [<=] comparison -- then maps can be implemented with
    _binary search trees_ (BSTs).  Insert and lookup operations on
    BSTs take time proportional to the height of the tree.  If the
    tree is balanced, the operations therefore take logarithmic time. *)

(** If you don't recall BSTs or haven't seen them in a while, see
    Wikipedia or read any standard textbook; for example:

    - Section 3.2 of _Algorithms, Fourth Edition_, by Sedgewick and
      Wayne, Addison Wesley 2011; or

    - Chapter 12 of _Introduction to Algorithms, 3rd Edition_, by
      Cormen, Leiserson, and Rivest, MIT Press 2009. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import String.  (* for an example, and manual grading *)
From Coq Require Import Logic.FunctionalExtensionality.
(**
From VFA Require Import Perm.
From VFA Require Import Maps.
From VFA Require Import Sort.
**)

(** * Sort: Insertion Sort *)

(** Sorting can be done in expected O(N log N) time by various
    algorithms (quicksort, mergesort, heapsort, etc.).  But for
    smallish inputs, a simple quadratic-time algorithm such as
    insertion sort can actually be faster.  It's certainly easier to
    implement -- and to verify. *)

(** If you don't recall insertion sort or haven't seen it in
    a while, see Wikipedia or read any standard textbook; for example:

    - Sections 2.0 and 2.1 of _Algorithms, Fourth Edition_, by
      Sedgewick and Wayne, Addison Wesley 2011; or

    - Section 2.1 of _Introduction to Algorithms, 3rd Edition_, by
      Cormen, Leiserson, and Rivest, MIT Press 2009. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
(**From VFA Require Import Perm.
**)
(** * Perm: Basic Techniques for Comparisons and Permutations *)

(** Consider these algorithms and data structures:
    - sort a sequence of numbers
    - finite maps from numbers to (arbitrary-type) data
    - finite maps from any ordered type to (arbitrary-type) data
    - priority queues: finding/deleting the highest number in a set

    To prove the correctness of such programs, we need to reason about
    comparisons, and about whether two collections have the same
    contents.  In this chapter, we introduce some techniques for
    reasoning about:

    - less-than comparisons on natural numbers, and
    - permutations (rearrangements of lists).

    In later chapters, we'll apply these proof techniques to reasoning
    about algorithms and data structures. *)

(* ################################################################# *)
(** * The Coq Standard Library *)

(** In this volume, we're going to import the definitions and theorems
    we need directly from Coq's standard library, rather than from
    chapters in Volume 1.  You should not notice much difference,
    though, because we've been careful to name our own definitions and
    theorems the same as their counterparts in the standard
    library. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.  (* for manual grading *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.PeanoNat.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
Export ListNotations.
From Coq Require Export Permutation.

(* ################################################################# *)
(** * The Less-Than Order on the Natural Numbers *)

(** In our proofs about searching and sorting algorithms, we
    often have to reason about the less-than order on natural numbers.
    Recall that the Coq standard library contains both propositional
    and Boolean less-than operators on natural numbers.  We write [x <
    y] for the proposition that [x] is less than [y]: *)

Locate "_ < _". (* "x < y" := lt x y *)
Check lt : nat -> nat -> Prop.

(** And we write [x <? y] for the computation that returns [true] or
    [false] depending on whether [x] is less than [y]: *)

Locate "_ <? _". (* x <? y  := Nat.ltb x y *)
Check Nat.ltb : nat -> nat -> bool.

(** Operation [<] is a reflection of [<?], as discussed in
    [Logic] and [IndProp]. The [Nat] module has a
    theorem showing how they relate: *)

Check Nat.ltb_lt : forall n m : nat, (n <? m) = true <-> n < m.

(** The [Nat] module contains a synonym for [lt]. *)

Print Nat.lt. (* Nat.lt = lt *)

(** For unknown reasons, [Nat] does not define [>=?] or [>?].  So we
    define them here: *)

Definition geb (n m : nat) := m <=? n.
Hint Unfold geb : core.
Infix ">=?" := geb (at level 70) : nat_scope.

Definition gtb (n m : nat) := m <? n.
Hint Unfold gtb : core.
Infix ">?" := gtb (at level 70) : nat_scope.

(* ================================================================= *)
(** ** The Lia Tactic *)

(** Reasoning about inequalities by hand can be a little painful. Luckily, Coq
    provides a tactic called [lia] that is quite helpful. *)

Theorem lia_example1:
 forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
   k > i.
Proof.
  intros.

(** The hard way to prove this is by hand. *)

  (* try to remember the name of the lemma about negation and [<=] *)
  Search (~ _ <= _ -> _).
  apply not_le in H0.
  (* [>] is defined using [<]. Let's convert all inequalities to [<]. *)
  unfold gt in H0.
  unfold gt.
  (* try to remember the name of the transitivity lemma about [>] *)
  Search (_ < _ -> _ < _ -> _ < _).
  apply Nat.lt_trans with j.
  apply H.
  apply Nat.lt_trans with (k-3).
  apply H0.
  (* Is [k] greater than [k-3]? On the integers, sure. But we're working
     with natural numbers, which truncate subtraction at zero. *)
Abort.

Theorem truncated_subtraction: ~ (forall k:nat, k > k - 3).
Proof.
  intros contra.
  (* [specialize] applies a hypothesis to an argument *)
  specialize (contra 0).
  simpl in contra.
  inversion contra.
Qed.

(** Since subtraction is truncated, does [lia_example1] actually hold?
    It does. Let's try again, the hard way, to find the proof. *)

Theorem lia_example1:
 forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
   k > i.
Proof. (* try again! *)
  intros.
  apply not_le in H0.
  unfold gt in H0.
  unfold gt.
  (* try to remember the name ... *)
  Search (_ < _ -> _ <= _ -> _ < _).
  apply Nat.lt_le_trans with j.
  apply H.
  apply Nat.le_trans with (k-3).
  Search (_ < _ -> _ <= _).
  apply Nat.lt_le_incl.
  auto.
  apply Nat.le_sub_l.
Qed.

(** That was tedious.  Here's a much easier way: *)

Theorem lia_example2:
 forall i j k,
    i < j ->
    ~ (k - 3 <= j) ->
   k > i.
Proof.
  intros.
  lia.
Qed.

(** Lia is a decision procedure for integer linear arithemetic.
    The [lia] tactic was made available by importing [Lia] at the
    beginning of the file.  The tactic
    works with Coq types [Z] and [nat], and these operators: [<] [=] [>]
    [<=] [>=] [+] [-] [~], as well as multiplication by small integer
    literals (such as 0,1,2,3...), and some uses of [\/], [/\], and [<->].

    Lia does not "understand" other operators.  It treats
    expressions such as [f x y] as variables.  That is, it
    can prove [f x y > a * b -> f x y + 3 >= a * b], in the same way it
    would prove [u > v -> u + 3 >= v].
*)

Theorem lia_example_3 : forall (f : nat -> nat -> nat) a b x y,
    f x y > a * b -> f x y + 3 >= a * b.
Proof.
  intros. lia.
Qed.



(* ################################################################# *)
(** * Swapping *)

(** Consider trying to sort a list of natural numbers.  As a small piece of
    a sorting algorithm, we might need to swap the first two elements of a list
    if they are out of order. *)

Definition maybe_swap (al: list nat) : list nat :=
  match al with
  | a :: b :: ar => if a >? b then b :: a :: ar else a :: b :: ar
  | _ => al
  end.

Example maybe_swap_123:
  maybe_swap [1; 2; 3] = [1; 2; 3].
Proof. reflexivity. Qed.

Example maybe_swap_321:
  maybe_swap [3; 2; 1] = [2; 3; 1].
Proof. reflexivity. Qed.

(** Applying [maybe_swap] twice should give the same result as applying it once.
    That is, [maybe_swap] is _idempotent_. *)

Theorem maybe_swap_idempotent: forall al,
    maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros [ | a [ | b al]]; simpl; try reflexivity.
  destruct (a >? b) eqn:H1; simpl.
  - destruct (b >? a) eqn:H2; simpl.
    + (** Now what?  We have a contradiction in the hypotheses: it
          cannot hold that [a] is less than [b] and [b] is less than
          [a].  Unfortunately, [lia] cannot immediately show that
          for us, because it reasons about comparisons in [Prop] not
          [bool]. *)
      Fail lia.
Abort.

(** Of course we could finish the proof by reasoning directly about
    inequalities in [bool].  But this situation is going to occur
    repeatedly in our study of sorting. *)

(** Let's set up some machinery to enable using [lia] on boolean
    tests. *)

(* ================================================================= *)
(** ** Reflection *)

(** The [reflect] type, defined in the standard library (and presented
    in [IndProp]), relates a proposition to a Boolean. That is,
    a value of type [reflect P b] contains a proof of [P] if [b] is
    [true], or a proof of [~ P] if [b] is [false]. *)

Print reflect.

(*
Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT :   P -> reflect P true
  | ReflectF : ~ P -> reflect P false
 *)

(** The standard library proves a theorem that says if [P] is provable
    whenever [b = true] is provable, then [P] reflects [b]. *)

Check iff_reflect : forall (P : Prop) (b : bool),
    P <-> b = true -> reflect P b.

(** Using that theorem, we can quickly prove that the propositional
    (in)equality operators are reflections of the Boolean
    operators. *)

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Lemma gtb_reflect : forall x y, reflect (x > y) (x >? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma geb_reflect : forall x y, reflect (x >= y) (x >=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

(** Here's an example of how you could use these lemmas.  Suppose you
    have this simple program, [(if a <? 5 then a else 2)], and you
    want to prove that it evaluates to a number smaller than 6.  You
    can use [ltb_reflect] "by hand": *)

Example reflect_example1: forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros a.
  (* The next two lines aren't strictly necessary, but they
     help make it clear what [destruct] does. *)
  assert (R: reflect (a < 5) (a <? 5)) by apply ltb_reflect.
  remember (a <? 5) as guard.
  destruct R as [H|H] eqn:HR.
  * (* ReflectT *) lia.
  * (* ReflectF *) lia.
Qed.

(** For the [ReflectT] constructor, the guard [a <? 5] must be equal
    to [true]. The [if] expression in the goal has already been
    simplified to take advantage of that fact. Also, for [ReflectT] to
    have been used, there must be evidence [H] that [a < 5] holds.
    From there, all that remains is to show [a < 5] entails [a < 6].
    The [lia] tactic, which is capable of automatically proving some
    theorems about inequalities, succeeds.

    For the [ReflectF] constructor, the guard [a <? 5] must be equal
    to [false]. So the [if] expression simplifies to [2 < 6], which is
    immediately provable by [lia]. *)

(** A less didactic version of the above proof wouldn't do the
    [assert] and [remember]: we can directly skip to [destruct]. *)

Example reflect_example1': forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros a. destruct (ltb_reflect a 5); lia.
Qed.

(** But even that proof is a little unsatisfactory. The original expression,
    [a <? 5], is not perfectly apparent from the expression [ltb_reflect a 5]
    that we pass to [destruct]. *)

(** It would be nice to be able to just say something like [destruct
    (a <? 5)] and get the reflection "for free."  That's what we'll
    engineer, next. *)

(* ================================================================= *)
(** ** A Tactic for Boolean Destruction *)

(** We're now going to build a tactic that you'll want to _use_, but
    you won't need to understand the details of how to _build_ it
    yourself.

    Let's put several of these [reflect] lemmas into a Hint database.
    We call it [bdestruct], because we'll use it in our
    boolean-destruction tactic: *)

Hint Resolve ltb_reflect leb_reflect gtb_reflect geb_reflect eqb_reflect : bdestruct.

(** Here is the tactic, the body of which you do not need to
    understand.  Invoking [bdestruct] on Boolean expression [b] does
    the same kind of reasoning we did above: reflection and
    destruction.  It also attempts to simplify negations involving
    inequalities in hypotheses. *)

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(** This tactic makes quick, easy-to-read work of our running example. *)

Example reflect_example2: forall a,
    (if a <? 5 then a else 2) < 6.
Proof.
  intros.
  bdestruct (a <? 5);  (* instead of: [destruct (ltb_reflect a 5)]. *)
  lia.
Qed.

(* ================================================================= *)
(** ** Finishing the [maybe_swap] Proof *)

(** Now that we have [bdestruct], we can finish the proof of [maybe_swap]'s
    idempotence. *)

Theorem maybe_swap_idempotent: forall al,
    maybe_swap (maybe_swap al) = maybe_swap al.
Proof.
  intros [ | a [ | b al]]; simpl; try reflexivity.
  bdestruct (a >? b); simpl.
  (** Note how [a > b] is a hypothesis, rather than [a >? b = true]. *)
  - bdestruct (b >? a); simpl.
    + (** [lia] can take care of the contradictory propositional inequalities. *)
      lia.
    + reflexivity.
  - bdestruct (a >? b); simpl.
    + lia.
    + reflexivity.
Qed.

(** When proving theorems about a program that uses Boolean
    comparisons, use [bdestruct] followed by [lia], rather than
    [destruct] followed by application of various theorems about
    Boolean operators. *)

(* ################################################################# *)
(** * Permutations *)

(** Another useful fact about [maybe_swap] is that it doesn't add or
    remove elements from the list: it only reorders them.  That is,
    the output list is a permutation of the input.  List [al] is a
    _permutation_ of list [bl] if the elements of [al] can be
    reordered to get the list [bl].  Note that reordering does not
    permit adding or removing duplicate elements. *)

(** Coq's [Permutation] library has an inductive definition of
    permutations. *)

Print Permutation.

(*
 Inductive Permutation {A : Type} : list A -> list A -> Prop :=
  | perm_nil : Permutation [] []
  | perm_skip : forall (x : A) (l l' : list A),
                Permutation l l' ->
                Permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) (l : list A),
                Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall l l' l'' : list A,
                 Permutation l l' ->
                 Permutation l' l'' ->
                 Permutation l l''.
 *)

(** You might wonder, "is that really the right definition?"  And
    indeed, it's important that we get a right definition, because
    [Permutation] is going to be used in our specifications of
    searching and sorting algorithms.  If we have the wrong
    specification, then all our proofs of "correctness" will be
    useless.

    It's not obvious that this is indeed the right specification of
    permutations. (It happens to be, but that's not obvious.) To gain
    confidence that we have the right specification, let's use it
    prove some properties that permutations ought to have. *)

(** **** Exercise: 2 stars, standard (Permutation_properties)

    Think of some desirable properties of the [Permutation] relation
    and write them down informally in English, or a mix of Coq and
    English.  Here are four to get you started:

     - 1. If [Permutation al bl], then [length al = length bl].
     - 2. If [Permutation al bl], then [Permutation bl al].
     - 3. [[1;1]] is NOT a permutation of [[1;2]].
     - 4. [[1;2;3;4]] IS a permutation of [[3;4;2;1]].

   YOUR TASK: Add three more properties. Write them here: *)

(** Now, let's examine all the theorems in the Coq library about
    permutations: *)

Search Permutation.  (* Browse through the results of this query! *)

(** Which of the properties that you wrote down above have already
    been proved as theorems by the Coq library developers?  Answer
    here:

*)
(* Do not modify the following line: *)
Definition manual_grade_for_Permutation_properties : option (nat*string) := None.
(** [] *)

(** Let's use the permutation theorems in the library to prove the
    following theorem. *)

Example butterfly: forall b u t e r f l y : nat,
  Permutation ([b;u;t;t;e;r]++[f;l;y]) ([f;l;u;t;t;e;r]++[b;y]).
Proof.
  intros.
  (** Let's group [[u;t;t;e;r]] together on both sides.  Tactic
      [change t with u] replaces [t] with [u].  Terms [t] and [u] must
      be _convertible_, here meaning that they evaluate to the same
      term. *)
  change [b;u;t;t;e;r] with ([b]++[u;t;t;e;r]).
  change [f;l;u;t;t;e;r] with ([f;l]++[u;t;t;e;r]).

  (** We don't actually need to know the list elements in
      [[u;t;t;e;r]].  Let's forget about them and just remember them
      as a variable named [utter]. *)
  remember [u;t;t;e;r] as utter. clear Hequtter.

  (** Likewise, let's group [[f;l]] and remember it as a variable. *)
  change [f;l;y] with ([f;l]++[y]).
  remember [f;l] as fl. clear Heqfl.

  (** Next, let's cancel [fl] from both sides.  In order to do that,
      we need to bring it to the beginning of each list. For the right
      list, that follows easily from the associativity of [++].  *)
  replace ((fl ++ utter) ++ [b;y]) with (fl ++ utter ++ [b;y])
    by apply app_assoc.

  (** But for the left list, we can't just use associativity.
      Instead, we need to reason about permutations and use some
      library theorems. *)
  apply perm_trans with (fl ++ [y] ++ ([b] ++ utter)).
  - replace (fl ++ [y] ++ [b] ++ utter) with ((fl ++ [y]) ++ [b] ++ utter).
    + apply Permutation_app_comm.
    + rewrite <- app_assoc. reflexivity.

  - (** A library theorem will now help us cancel [fl]. *)
    apply Permutation_app_head.

  (** Next let's cancel [utter]. *)
    apply perm_trans with (utter ++ [y] ++ [b]).
    + replace ([y] ++ [b] ++ utter) with (([y] ++ [b]) ++ utter).
      * apply Permutation_app_comm.
      * rewrite app_assoc. reflexivity.
    + apply Permutation_app_head.

      (** Finally we're left with just [y] and [b]. *)
      apply perm_swap.
Qed.

(** That example illustrates a general method for proving permutations
    involving cons [::] and append [++]:

    - Identify some portion appearing in both sides.
    - Bring that portion to the front on each side using lemmas such
      as [Permutation_app_comm] and [perm_swap], with generous use of
      [perm_trans].
    - Use [Permutation_app_head] to cancel an appended head.  You can
      also use [perm_skip] to cancel a single element. *)

(** **** Exercise: 3 stars, standard (permut_example)

    Use the permutation rules in the library to prove the following
    theorem.  The following [Check] commands are a hint about useful
    lemmas.  You don't need all of them, and depending on your
    approach you will find some lemmas to be more useful than others.
    Use [Search] to find others, if you like. *)

Check perm_skip.
Check perm_trans.
Check Permutation_refl.
Check Permutation_app_comm.
Check app_assoc.
Check app_nil_r.
Check app_comm_cons.

Example permut_example: forall (a b: list nat),
  Permutation (5 :: 6 :: a ++ b) ((5 :: b) ++ (6 :: a ++ [])).
Proof.
  intros. apply perm_skip. rewrite app_nil_r. apply perm_trans with (b ++(6::a)).
  - rewrite app_comm_cons. apply Permutation_app_comm. 
  - reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (not_a_permutation)

    Prove that [[1;1]] is not a permutation of [[1;2]].
    Hints are given as [Check] commands. *)

Check Permutation_cons_inv.
Check Permutation_length_1_inv.

Example not_a_permutation:
  ~ Permutation [1;1] [1;2].
Proof.
  unfold not. intros Hyp.
  assert (H: Permutation [1] [2]).
  - apply Permutation_cons_inv with 1. apply Hyp.
  - apply Permutation_length_1_inv in H. inversion H.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Correctness of [maybe_swap] *)

(** Now we can prove that [maybe_swap] is a permutation: it reorders
    elements but does not add or remove any. *)

Theorem maybe_swap_perm: forall al,
  Permutation al (maybe_swap al).
Proof.
  (* WORKED IN CLASS *)
  unfold maybe_swap.
  destruct al as [ | a [ | b al]].
  - simpl. apply perm_nil.
  - apply Permutation_refl.
  - bdestruct (a >? b).
    + apply perm_swap.
    + apply Permutation_refl.
Qed.

(** And, we can prove that [maybe_swap] permutes elements such that
    the first is less than or equal to the second. *)

Definition first_le_second (al: list nat) : Prop :=
  match al with
  | a :: b :: _ => a <= b
  | _ => True
  end.

Theorem maybe_swap_correct: forall al,
    Permutation al (maybe_swap al)
    /\ first_le_second (maybe_swap al).
Proof.
  intros. split.
  - apply maybe_swap_perm.
  - (* WORKED IN CLASS *)
    unfold maybe_swap.
    destruct al as [ | a [ | b al]]; simpl; auto.
    bdestruct (a >? b); simpl; lia.
Qed.

(* ################################################################# *)
(** * An Inversion Tactic *)

(** Coq's [inversion H] tactic is so good at extracting
    information from the hypothesis [H] that [H] sometimes becomes
    completely redundant, and one might as well [clear] it from the
    goal.  Then, since the [inversion] typically creates some equality
    facts, why not [subst]?  Tactic [inv] does just that. *)

Ltac inv H := inversion H; clear H; subst.

(** **** Exercise: 3 stars, standard (Forall_perm) *)

(** [Forall] is Coq library's version of the [All] proposition defined
    in [Logic], but defined as an inductive proposition rather
    than a fixpoint.  Prove this lemma by induction.  You will need to
    decide what to induct on: [al], [bl], [Permutation al bl], and
    [Forall f al] are possibilities. *)

Theorem Forall_perm: forall {A} (f: A -> Prop) al bl,
  Permutation al bl ->
  Forall f al -> Forall f bl.
Proof.
  intros. induction H.
  - apply H0.
  - inversion H0. constructor. 
    -- apply H3.
    -- apply IHPermutation. apply H4.
  - inversion H0. constructor.
    -- inversion H3. apply H6.
    -- inversion H0. constructor. 
      --- apply H6.
      --- inv H3. apply H11.
  - apply IHPermutation2. apply IHPermutation1. apply H0.
Qed.
(** [] *)

(* ################################################################# *)
(** * Summary: Comparisons and Permutations *)

(** To prove correctness of algorithms for sorting and searching,
    we'll reason about comparisons and permutations using the tools
    developed in this chapter.  The [maybe_swap] program is a tiny
    little example of a sorting program.  The proof style in
    [maybe_swap_correct] will be applied (at a larger scale) in
    the next few chapters. *)

(* 2024-08-25 08:38 *)

(* ################################################################# *)
(** * The Insertion-Sort Program *)

(** Insertion sort is usually presented as an imperative program
    operating on arrays.  But it works just as well as a functional
    program operating on linked lists. *)

(* [insert i l] inserts [i] into its sorted place in list [l].
   Precondition: [l] is sorted. *)
Fixpoint insert (i : nat) (l : list nat) :=
  match l with
  | [] => [i]
  | h :: t => if i <=? h then i :: h :: t else h :: insert i t
  end.

Fixpoint sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (sort t)
  end.

Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof. simpl. reflexivity. Qed.

(** What Sedgewick/Wayne and Cormen/Leiserson/Rivest don't acknowlege
    is that the arrays-and-swaps model of sorting is not the only one
    in the world.  We are writing _functional programs_, where our
    sequences are (typically) represented as linked lists, and where
    we do _not_ destructively splice elements into those lists. *)

(** As usual with functional lists, the output of [sort] may share
    memory with the input.  For example: *)

Compute insert 7 [1; 3; 4; 8; 12; 14; 18].
(* = [1; 3; 4; 7; 8; 12; 14; 18] *)

(** The tail of this list, [12 :: 14 :: 18 :: []], is not disturbed or
    rebuilt by the [insert] algorithm.  The head [1 :: 3 :: 4 :: 7 :: ...]
    contains new nodes constructed by [insert].  The first three nodes
    of the old list, [1 :: 3 :: 4 :: ...], will likely be
    garbage-collected if no other data structure is still pointing at
    them.  Thus, in this typical case,

     - Time cost = 4X

     - Space cost = (4-3)Y = Y

    where X and Y are constants, independent of the length of the
    tail.  The value Y is the number of bytes in one list node: 2 to 4
    words, depending on how the implementation handles
    constructor-tags.  We write (4-3) to indicate that four list nodes
    are constructed, while three list nodes become eligible for
    garbage collection.

    We will not prove such things about the time and space cost, but
    they are true anyway, and we should keep them in consideration. *)

(* ################################################################# *)
(** * Specification of Correctness *)

(** A sorting algorithm must rearrange the elements into a list
    that is totally ordered. There are many ways we might express that
    idea formally in Coq.  One is with an inductively-defined
    relation that says: *)

(** - The empty list is sorted.

    - Any single-element list is sorted.

    - For any two adjacent elements, they must be in the proper order. *)

Inductive sorted : list nat -> Prop :=
| sorted_nil :
    sorted []
| sorted_1 : forall x,
    sorted [x]
| sorted_cons : forall x y l,
    x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Hint Constructors sorted : core.

(** This definition might not be the most obvious. Another
    definition, perhaps more familiar, might be: for any two elements
    of the list (regardless of whether they are adjacent), they should
    be in the proper order.  Let's try formalizing that.

    We can think in terms of indices into a list [lst], and say: for
    any valid indices [i] and [j], if [i < j] then [index lst i <=
    index lst j], where [index lst n] means the element of [lst] at
    index [n].  Unfortunately, formalizing this idea becomes messy,
    because any Coq function implementing [index] must be total: it
    must return some result even if the index is out of range for the
    list.  The Coq standard library contains two such functions: *)

Check nth : forall A : Type, nat -> list A -> A -> A.
Check nth_error : forall A : Type, list A -> nat -> option A.

(** These two functions ensure totality in different ways:

    - [nth] takes an additional argument of type [A] --a _default_
      value-- to be returned if the index is out of range, whereas

    - [nth_error] returns [Some v] if the index is in range and [None]
      --an error-- otherwise.

    If we use [nth], we must ensure that indices are in range: *)

Definition sorted'' (al : list nat) := forall i j,
    i < j < length al ->
    nth i al 0 <= nth j al 0.

(** The choice of default value, here 0, is unimportant, because it
    will never be returned for the [i] and [j] we pass.

    If we use [nth_error], we must add additional antecedents: *)

Definition sorted' (al : list nat) := forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

(** Here, the validity of [i] and [j] are implicit in the fact
    that we get [Some] results back from each call to [nth_error]. *)

(** All three definitions of sortedness are reasonable.  In practice,
    [sorted'] is easier to work with than [sorted''] because it
    doesn't need to mention the [length] function. And [sorted] is
    easiest, because it doesn't need to mention indices. *)

(** Using [sorted], we specify what it means to be a correct sorting
    algorthm: *)

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

(** Function [f] is a correct sorting algorithm if [f al] is
    [sorted] and is a permutation of its input. *)

(* ################################################################# *)
(** * Proof of Correctness *)

(** In the following exercises, you will prove the correctness of
    insertion sort. *)

(** **** Exercise: 3 stars, standard (insert_sorted) *)

(* Prove that insertion maintains sortedness. Make use of tactic
   [bdestruct], defined in [Perm]. *)

Lemma insert_sorted:
  forall a l, sorted l -> sorted (insert a l).
Proof.
  intros a l S. induction S.
  -simpl. constructor.
  -destruct (a <=? x) eqn:Ha.
    + simpl. rewrite Ha. simpl. constructor.
      * apply Nat.leb_le. apply Ha.
      * constructor. 
    + simpl. rewrite Ha. simpl. constructor. 
      -- apply Nat.leb_gt in Ha. apply Nat.lt_le_incl. apply Ha. -- constructor.
  -destruct (a <=? x) eqn:Ha.
    + simpl. rewrite Ha. simpl. constructor.
      * apply Nat.leb_le. apply Ha.
      * simpl. apply sorted_cons. --- apply H. --- apply S.
    + simpl. rewrite Ha. simpl. simpl in IHS. destruct (a <=? y) eqn:Hay.
      * apply sorted_cons.
        ---- apply Nat.leb_gt in Ha. apply Nat.lt_le_incl. apply Ha.
        ---- apply IHS.
      * apply sorted_cons. 
        ---- apply H.
        ---- apply IHS.
Qed.


(** [] *)

(** **** Exercise: 2 stars, standard (sort_sorted) *)

(** Using [insert_sorted], prove that insertion sort makes a list
    sorted. *)

Theorem sort_sorted: forall l, sorted (sort l).
Proof.
  intros. induction l as [| x l' IH].
    - simpl. constructor.
    - simpl. apply insert_sorted. apply IH.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (insert_perm) *)

(** The following lemma will be useful soon as a helper. Take
    advantage of helpful theorems from the [Permutation] library. *)

Lemma insert_perm: forall x l,
    Permutation (x :: l) (insert x l).
Proof.
  intros. induction l as [| xhead l' IH].
  - simpl. apply Permutation_refl.
  - simpl. destruct (x <=? xhead) eqn:Hyp.
    + apply Permutation_refl.
    + apply perm_trans with (xhead :: x :: l').
      * apply perm_swap.
      * apply perm_skip. apply IH.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (sort_perm) *)

(** Prove that [sort] is a permutation, using [insert_perm]. *)

Theorem sort_perm: forall l, Permutation l (sort l).
Proof.
  intros. induction l as [| x xs IH].
  - simpl. apply Permutation_refl.
  - simpl. apply Permutation_trans with (x :: sort xs).
    * apply perm_skip. apply IH.
    * apply insert_perm.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (insertion_sort_correct) *)

(** Finish the proof of correctness! *)

Theorem insertion_sort_correct:
    is_a_sorting_algorithm sort.
Proof.
  unfold is_a_sorting_algorithm. intros. split.
  - apply sort_perm.
  - apply sort_sorted.
Qed.

(** [] *)

(* ################################################################# *)
(** * Validating the Specification (Advanced) *)

(** You can prove that a program satisfies a specification, but how
    can you prove you have the right specification?  Actually, you
    cannot.  The specification is an informal requirement in your
    mind.  As Alan Perlis quipped, "One can't proceed from the
    informal to the formal by formal means."

    But one way to build confidence in a specification is to state it
    in two different ways, then prove they are equivalent. *)

(** **** Exercise: 4 stars, advanced (sorted_sorted') *)
Lemma sorted_sorted': forall al, sorted al -> sorted' al.

(** Hint: Instead of doing induction on the list [al], do induction on
    the sortedness of [al]. This proof is a bit tricky, so you may
    have to think about how to approach it, and try out one or two
    different ideas.*)
Proof.
  intros al H.
  induction H.
  - unfold sorted'. intros i j iv jv H1 H2 H3.
    simpl in H2, H3. destruct i; inversion H2; destruct j; inversion H3.
  - unfold sorted'. intros i j iv jv H1 H2 H3. destruct i, j. inversion H2; inversion H3; subst.
    + apply le_n.
    + destruct j.
      * simpl in H3. inversion H3.
      * simpl in H3. inversion H3.
    + simpl in H2. destruct i.
      * simpl in H2. inversion H2.
      * simpl in H2. inversion H2.
    + simpl in H2. simpl in H3. destruct i,j. 
      --- inversion H2.
      --- inversion H2.
      --- inversion H2.
      --- inversion H2.
  - unfold sorted'. intros i j iv jv Hle Hnth1 Hnth2.
    destruct i.
    + simpl in Hnth1. inversion Hnth1; subst iv.
      destruct j.
      * simpl in Hnth2. inversion Hnth2; subst jv.
        apply le_n.
      * simpl in Hnth2.
        assert (Hnth_jv: nth_error (y :: l) (j) = Some jv) by assumption.
        assert (Hsorted'_y_l: sorted' (y :: l)) by apply IHsorted. Admitted.

(** **** Exercise: 3 stars, advanced (sorted'_sorted) *)
Lemma sorted'_sorted : forall al, sorted' al -> sorted al.
Proof.
(** Here, you can't do induction on the sortedness of the list,
    because [sorted'] is not an inductive predicate. But the proof
    is less tricky than the previous. *)
  intros al H.
  induction al as [| x xs IH].
  - apply sorted_nil.
  - destruct xs as [| y ys].
    + apply sorted_1.
    + assert (Hxy: x <= y).
      { unfold sorted' in H. apply (H 0 1 x y); try lia; reflexivity. }
      apply sorted_cons.
      * exact Hxy.
      * apply IH. unfold sorted' in *. intros i j iv jv Hlt Hnth1 Hnth2. apply (H (S i) (S j) iv jv).
        ** lia.
        ** simpl. apply Hnth1.
        ** simpl. apply Hnth2.
Qed.
(** [] *)

(* ################################################################# *)
(** * Proving Correctness from the Alternative Spec (Optional) *)

(** Depending on how you write the specification of a program, it can
    be harder or easier to prove correctness.  We saw that predicates
    [sorted] and [sorted'] are equivalent.  It is significantly
    harder, though, to prove correctness of insertion sort directly
    from [sorted'].

    Give it a try!  The best proof we know of makes essential use of
    the auxiliary lemma [nth_error_insert], so you may want to prove
    that first.  And some other auxiliary lemmas may be needed too.
    But maybe you will find a simpler appraoch!

    DO NOT USE [sorted_sorted'], [sorted'_sorted], [insert_sorted], or
    [sort_sorted] in these proofs.  That would defeat the purpose! *)

(** **** Exercise: 5 stars, standard, optional (insert_sorted') *)

Lemma nth_error_insert : forall l a i iv,
    nth_error (insert a l) i = Some iv ->
    a = iv \/ exists i', nth_error l i' = Some iv.
Proof.
(* FILL IN HERE *) Admitted.

Lemma insert_sorted':
  forall a l, sorted' l -> sorted' (insert a l).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

Theorem sort_sorted': forall l, sorted' (sort l).
Proof.
  induction l.
  - unfold sorted'. intros. destruct i; inv H0.
  - simpl. apply insert_sorted'. auto.
Qed.

(** If you complete the proofs above, you will note that the proof of
    [insert_sorted] is relatively easy compared to the proof of
    [insert_sorted'], even though [sorted al <-> sorted' al].  So,
    suppose someone asked you to prove [sort_sorted'].  Instead of
    proving it directly, it would be much easier to design predicate
    [sorted], then prove [sort_sorted] and [sorted_sorted'].

    The moral of the story is therefore: _Different formulations of
    the functional specification can lead to great differences in the
    difficulty of the correctness proofs_. *)


(* 2024-08-25 08:38 *)

(** The [Lists] chapter in Volume 1 previously
    implemented maps with lists of key-value pairs. Here, we instead
    use functions to implement maps. Functions enable an _extensional_
    treatment of maps: two maps will be equal if they take the keys to
    the same values. We won't have to worry about issues that arise
    with lists, such as duplicate keys, or order of pairs in the list,
    etc. Proofs that use maps will therefore be simpler.

    Intuitively, a total map over a type [A] _is_ just a function that
    can be used to look up keys, yielding [A]s.  For simplicity, the
    keys in our maps will be natural numbers. *)

Definition total_map (A : Type) : Type := nat -> A.

(** The function [t_empty] yields an empty total map, given a
    default element; this map always returns the default element when
    applied to any id. *)

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the [update] function, which (as before)
    takes a map [m], a key [x], and a value [v] and returns a new map
    that takes [x] to [v] and takes every other key to whatever [m]
    does. *)

Definition t_update {A : Type}
           (m : total_map A) (x : nat) (v : A) : total_map A :=
  fun x' => if x =? x' then v else m x'.

(** This definition is a nice example of higher-order programming.
    The [t_update] function takes a _function_ [m] and yields a new
    function [fun x' => ...] that behaves like the desired map.

    For example, we can build a map taking [id]s to [bool]s, where [Id 3]
    is mapped to [true] and every other key is mapped to [false], like
    this: *)

Definition examplemap :=
  t_update (t_update (t_empty false) 1 false) 3 true.

(** This completes the definition of total maps.  Note that we don't
    need to define a [find] operation because it is just function
    application! *)

Example update_example1 : examplemap 0 = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap 1 = false.
Proof. reflexivity. Qed.

Example update_example3 : examplemap 2 = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap 3 = true.
Proof. reflexivity. Qed.

(** To use maps in later chapters, we'll need several
    fundamental facts about how they behave.  Even if you don't work
    the following exercises, make sure you thoroughly understand the
    statements of the lemmas!  (Some of the proofs require the
    [functional_extensionality] axiom, which is discussed in the
    [Logic] chapter.)  *)

(** **** Exercise: 1 star, standard (t_apply_empty)

    The empty map returns its default element for all keys: *)
Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
Proof.
  intros. unfold t_empty. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (t_update_eq)

    If we update a map [m] at a key [x] with a new value [v] and then
    look up [x] in the map resulting from the [update], we get back
    [v]: *)

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros. unfold t_update. rewrite Nat.eqb_refl. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (t_update_neq)

    If we update a map [m] at a key [x1] and then look up a
    _different_ key [x2] in the resulting map, we get the same result
    that [m] would have given: *)

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof.
  intros. unfold t_update. destruct (Nat.eqb_spec x1 x2) as [Heq | Hneq'].
  - contradiction.
  - reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (t_update_shadow)

    If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  intros. unfold t_update. apply functional_extensionality. intros x'.
  destruct (Nat.eqb_spec x x').
  - reflexivity.
  - reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (t_update_same)

    If we update a map to assign key [x] the same value as it already
    has in [m], then the result is equal to [m]: *)

Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  intros. unfold t_update. apply functional_extensionality. intros x0.
  destruct (Nat.eqb_spec x x0) as [Heq | Hneq ].
  - rewrite Heq. reflexivity.
  - reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (t_update_permute)

    If we update a map [m] at two distinct keys, it doesn't matter in
    which order we do the updates. *)

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  intros. unfold t_update. apply functional_extensionality. intros x. destruct (Nat.eqb_spec x1 x)
  as [HeqX1 | HneqX1].
  - destruct (Nat.eqb_spec x2 x) as [HeqX2 | HneqX2].
    -- rewrite <-HeqX1 in HeqX2. contradiction.
    -- reflexivity.
  - destruct (Nat.eqb_spec x2 x) as [HeqX2 | HneqX2].
    -- reflexivity.
    -- reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Partial Maps *)

(** A partial map with elements of type [A] is simply a total map with
    elements of type [option A] and default element [None]. *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type}
           (m : partial_map A) (x : nat) (v : A) : partial_map A :=
  t_update m x (Some v).

(** We can easily lift all of the basic lemmas about total maps to
    partial maps.  *)

Lemma apply_empty : forall A x, @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq; auto.
Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.

(* 2024-08-25 08:38 *)

(* ################################################################# *)
(** * BST Implementation *)

(** We use [nat] as the key type in our implementation of BSTs,
    since it has a convenient total order [<=?] with lots of theorems
    and automation available. *)

Definition key := nat.

(** [E] represents the empty map.  [T l k v r] represents the
    map that binds [k] to [v], along with all the bindings in [l] and
    [r].  No key may be bound more than once in the map. *)

Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : key) (v : V) (r : tree V).

Arguments E {V}.
Arguments T {V}.

(** An example tree:

      4 -> "four"
      /        \
     /          \
  2 -> "two"   5 -> "five"
*)

Definition ex_tree : tree string :=
  (T (T E 2 "two" E) 4 "four" (T E 5 "five" E))%string.

(** [empty_tree] contains no bindings. *)

Definition empty_tree {V : Type} : tree V :=
  E.

(** [bound k t] is whether [k] is bound in [t]. *)

Fixpoint bound {V : Type} (x : key) (t : tree V) :=
  match t with
  | E => false
  | T l y v r => if x <? y then bound x l
                else if x >? y then bound x r
                     else true
  end.

(** [lookup d k t] is the value bound to [k] in [t], or is default
    value [d] if [k] is not bound in [t]. *)

Fixpoint lookup {V : Type} (d : V) (x : key) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => if x <? y then lookup d x l
                else if x >? y then lookup d x r
                     else v
  end.

(** [insert k v t] is the map containing all the bindings of [t] along
    with a binding of [k] to [v]. *)
(* Change made by myself. *)
Fixpoint insertTree {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if x <? y then T (insertTree x v l) y v' r
                 else if x >? y then T l y v' (insertTree x v r)
                      else T l x v r
  end.

(** Note that [insert] is a _functional_ aka _persistent_
    implementation: [t] is not changed. *)

Module Tests.

(** Here are some unit tests to check that BSTs behave the way we
    expect. *)

  Open Scope string_scope.

  Example bst_ex1 :
    insertTree 5 "five" (insertTree 2 "two" (insertTree 4 "four" empty_tree)) = ex_tree.
  Proof. reflexivity. Qed.

  Example bst_ex2 : lookup "" 5 ex_tree = "five".
  Proof. reflexivity. Qed.

  Example bst_ex3 : lookup "" 3 ex_tree = "".
  Proof. reflexivity. Qed.

  Example bst_ex4 : bound 3 ex_tree = false.
  Proof. reflexivity. Qed.

End Tests.

(** Although we can spot-check the behavior of BST operations with
    unit tests like these, we of course should prove general theorems
    about their correctness.  We will do that later in the chapter. *)

(* ################################################################# *)
(** * BST Invariant *)

(** The implementations of [lookup] and [insert] assume that
    values of type [tree] obey the _BST invariant_: for any non-empty
    node with key [k], all the values of the left subtree are less
    than [k] and all the values of the right subtree are greater than
    [k].  But that invariant is not part of the definition of
    [tree]. For example, the following tree is not a BST: *)

Module NotBst.
  Open Scope string_scope.

  Definition t : tree string :=
    T (T E 5 "five" E) 4 "four" (T E 2 "two" E).

  (** The [insert] function we wrote above would never produce
      such a tree, but we can still construct it by manually applying
      [T]. When we try to lookup [2] in that tree, we get the wrong
      answer, because [lookup] assumes [2] is in the left subtree: *)

  Example not_bst_lookup_wrong :
    lookup "" 2 t <> "two".
  Proof.
    simpl. unfold not. intros contra. discriminate.
  Qed.
End NotBst.

(** So, let's formalize the BST invariant. Here's one way to do
    so.  First, we define a helper [ForallT] to express that idea that
    a predicate holds at every node of a tree: *)

Fixpoint ForallT {V : Type} (P: key -> V -> Prop) (t: tree V) : Prop :=
  match t with
  | E => True
  | T l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

(** Second, we define the BST invariant:

    - An empty tree is a BST.

    - A non-empty tree is a BST if all its left nodes have a lesser
      key, its right nodes have a greater key, and the left and
      right subtrees are themselves BSTs. *)

Inductive BST {V : Type} : tree V -> Prop :=
| BST_E : BST E
| BST_T : forall l x v r,
    ForallT (fun y _ => y < x) l ->
    ForallT (fun y _ => y > x) r ->
    BST l ->
    BST r ->
    BST (T l x v r).

Hint Constructors BST : core.

(** Let's check that [BST] correctly classifies a couple of example
    trees: *)

Example is_BST_ex :
  BST ex_tree.
Proof.
  unfold ex_tree.
  repeat (constructor; try lia).
Qed.

Example not_BST_ex :
  ~ BST NotBst.t.
Proof.
  unfold NotBst.t. intros contra.
  inv contra. inv H3. lia.
Qed.

(** **** Exercise: 1 star, standard (empty_tree_BST) *)

(** Prove that the empty tree is a BST. *)

Theorem empty_tree_BST : forall (V : Type),
    BST (@empty_tree V).
Proof.
  intros. unfold empty_tree. constructor. 
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (insert_BST) *)

(** Prove that [insert] produces a BST, assuming it is given one.

    Start by proving this helper lemma, which says that [insert]
    preserves any node predicate. Proceed by induction on [t]. *)

Lemma ForallT_insert : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t -> forall (k : key) (v : V),
      P k v -> ForallT P (insertTree k v t).
Proof.
  intros. induction t.
  - simpl. split. -- apply H0. -- split; reflexivity.
  - simpl. bdestruct (k <? k0).
    + simpl. destruct H as [H_k0v0 [H_s1 H_s2]]. split.
      * apply H_k0v0.
      * split. apply IHt1. apply H_s1. apply H_s2.
    + bdestruct (k >? k0).
      * simpl. destruct H as [H_k0v0 [H_s1 H_s2]]. split.
        ** apply H_k0v0.
        ** split. apply H_s1. apply IHt2. apply H_s2.
      * simpl. split. *** apply H0. *** destruct H. apply H3.
Qed.

(** Now prove the main theorem. Proceed by induction on the evidence
    that [t] is a BST. *)

Theorem insert_BST : forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t -> BST (insertTree k v t).
Proof.
  intros. induction t.
  - simpl. constructor. 
    -- unfold ForallT. reflexivity.
    -- unfold ForallT. reflexivity.
    -- apply H.
    -- apply H.
  - simpl. bdestruct (k <? k0).
    -- constructor.
      --- apply ForallT_insert. * inversion H. apply H5. * apply H0.
      --- inversion H. apply H6.
      --- apply IHt1. inversion H. apply H7.
      --- inversion H. apply H8.
    -- bdestruct (k >? k0). 
      --- inversion H. constructor. * apply H6. * apply ForallT_insert. ** apply H7. ** apply H1.
          * apply H8. * apply IHt2. apply H9.
      --- inversion H. constructor.
          * assert (k = k0) by lia. subst. apply H6.
          * assert (k = k0) by lia. subst. apply H7.
          * apply H8.
          * apply H9.
Qed.

(** [] *)

(** Since [empty_tree] and [insert] are the only operations that
    create BSTs, we are guaranteed that any [tree] is a BST -- unless
    it was constructed manually with [T].  It would therefore make
    sense to limit the use of [T] to only within the tree operations,
    rather than expose it.  Coq, like OCaml and other functional
    languages, can do this with its module system.  See [ADT] for
    details. *)

(* ################################################################# *)
(** * Correctness of BST Operations *)

(** To prove the correctness of [lookup] and [bound], we need
    specifications for them.  We'll study two different techniques for
    that in this chapter.

    The first is called _algebraic specification_.  With it, we write
    down equations relating the results of operations.  For example,
    we could write down equations like the following to specify the
    [+] and [*] operations:

      (a + b) + c = a + (b + c)
      a + b = b + a
      a + 0 = a
      (a * b) * c = a * (b * c)
      a * b = b * a
      a * 1 = a
      a * 0 = 0
      a * (b + c) = a * b + a * c

    For BSTs, let's examine how [lookup] should interact with
    when applied to other operations.  It is easy to see what needs to
    be true for [empty_tree]: looking up any value at all in the empty
    tree should fail and return the default value:

      lookup d k empty_tree = d

    What about non-empty trees?  The only way to build a non-empty
    tree is by applying [insert k v t] to an existing tree [t]. So it
    suffices to describe the behavior of [lookup] on the result of an
    arbitrary [insert] operation. There are two cases.  If we look up
    the same key that was just inserted, we should get the value that
    was inserted with it:

      lookup d k (insert k v t) = v

    If we look up a different key than was just inserted, the insert
    should not affect the answer -- which should be the same as if we
    did the lookup in the original tree before the insert occured:

      lookup d k' (insert k v t) = lookup d k' t      if k <> k'

    These three basic equations specify the correct behavior of maps.
    Let's prove that they hold. *)

Theorem lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.
Proof.
  auto.
Qed.

Theorem lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insertTree k v t)  = v.
Proof.
  induction t; intros; simpl.
  - bdestruct (k <? k); bdestruct (k >? k); try lia; auto.
  - bdestruct (k0 <? k); bdestruct (k0 >? k); simpl; try lia; auto.
    + bdestruct (k0 <? k); bdestruct (k0 >? k); try lia; auto.
    + bdestruct (k0 <? k); bdestruct (k0 >? k); try lia; auto.
    + bdestruct (k0 <? k0); bdestruct (k0 >? k0); try lia; auto.
Qed.

(** The basic method of that proof is to repeatedly [bdestruct]
    everything in sight, followed by generous use of [lia] and
    [auto]. Let's automate that. *)

Ltac bdestruct_guard :=
  match goal with
  | |- context [ if ?X =? ?Y then _ else _ ] => bdestruct (X =? Y)
  | |- context [ if ?X <=? ?Y then _ else _ ] => bdestruct (X <=? Y)
  | |- context [ if ?X <? ?Y then _ else _ ] => bdestruct (X <? Y)
  | |- context [ if ?X >=? ?Y then _ else _ ] => bdestruct (X >=? Y)
  | |- context [ if ?X >? ?Y then _ else _ ] => bdestruct (X >? Y)
  end.

Ltac bdall :=
  repeat (simpl; bdestruct_guard; try lia; auto).

Theorem lookup_insert_eq' :
  forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insertTree k v t) = v.
Proof.
  induction t; intros; bdall.
Qed.

(** The tactic immediately pays off in proving the third
    equation. *)

Theorem lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
   k <> k' -> lookup d k' (insertTree k v t) = lookup d k' t.
Proof.
  induction t; intros; bdall.
Qed.

(** Perhaps surprisingly, the proofs of these results do not
    depend on whether [t] satisfies the BST invariant.  That's because
    [lookup] and [insert] follow the same path through the tree, so
    even if nodes are in the "wrong" place, they are consistently
    "wrong". *)

(** **** Exercise: 3 stars, standard, optional (bound_correct) *)

(** Specify and prove the correctness of [bound]. State and prove
    three theorems, inspired by those we just proved for [lookup]. If
    you have the right theorem statements, the proofs should all be
    quite easy -- thanks to [bdall]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_bound_correct : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard, optional (bound_default) *)

(** Prove that if [bound] returns [false], then [lookup] returns
    the default value. Proceed by induction on the tree. *)

Theorem bound_default :
  forall (V : Type) (k : key) (d : V) (t : tree V),
    bound k t = false ->
    lookup d k t = d.
Proof.
  induction t. intros. 
  - simpl. reflexivity.
  - bdall.
Qed.

(** [] *)

(* ################################################################# *)
(** * BSTs vs. Higher-order Functions (Optional) *)

(** The three theorems we just proved for [lookup] should seem
    familiar: we proved equivalent theorems in [Maps] for maps
    defined as higher-order functions. *)

(** - [lookup_empty] and [t_apply_empty] both state that the empty map
      binds all keys to the default value. *)

Check lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k empty_tree = d.

Check t_apply_empty : forall (V : Type) (k : key) (d : V),
    t_empty d k = d.

(** - [lookup_insert_eq] and [t_update_eq] both state that updating a map
      then looking for the updated key produces the updated value. *)

Check lookup_insert_eq : forall (V : Type) (t : tree V) (d : V) (k : key) (v : V),
    lookup d k (insertTree k v t) = v.

Check t_update_eq : forall (V : Type) (m : total_map V) (k : key) (v : V),
    (t_update m k v) k = v.

(** - [lookup_insert_neq] and [t_update_neq] both state that updating
      a map then looking for a different key produces the same value
      as the original map. *)

Check lookup_insert_neq :
  forall (V : Type) (t : tree V) (d : V) (k k' : key) (v : V),
    k <> k' -> lookup d k' (insertTree k v t) = lookup d k' t.

Check t_update_neq : forall (V : Type) (v : V) (k k' : key) (m : total_map V),
    k <> k' -> (t_update m k v) k' = m k'.

(** In [Maps], we also proved three other theorems about the
    behavior of functional maps on various combinations of updates and
    lookups: *)

Check t_update_shadow : forall (V : Type) (m : total_map V) (v1 v2 : V) (k : key),
    t_update (t_update m k v1) k v2 = t_update m k v2.

Check t_update_same : forall (V : Type) (k : key) (m : total_map V),
    t_update m k (m k) = m.

Check t_update_permute :
  forall (V : Type) (v1 v2 : V) (k1 k2 : key) (m : total_map V),
    k2 <> k1 ->
    t_update (t_update m k2 v2) k1 v1 = t_update (t_update m k1 v1) k2 v2.

(** Let's prove analogues to these three theorems for search trees.

    Hint: you do not need to unfold the definitions of [empty_tree],
    [insert], or [lookup].  Instead, use [lookup_insert_eq] and
    [lookup_insert_neq]. *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_shadow) *)

Lemma lookup_insert_shadow :
  forall (V : Type) (t : tree V) (v v' d: V) (k k' : key),
    lookup d k' (insertTree k v (insertTree k v' t)) = lookup d k' (insertTree k v t).
Proof.
  intros. bdestruct (k =? k').
  - induction t.
    -- simpl. bdall.
    -- simpl. bdall.
  - induction t.
    -- simpl. bdall.
    -- simpl. bdall.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_same) *)

Lemma lookup_insert_same :
  forall (V : Type) (k k' : key) (d : V) (t : tree V),
    lookup d k' (insertTree k (lookup d k t) t) = lookup d k' t.
Proof.
  intros. induction t.
  - simpl. bdall.
  - simpl. bdall.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard, optional (lookup_insert_permute) *)

Lemma lookup_insert_permute :
  forall (V : Type) (v1 v2 d : V) (k1 k2 k': key) (t : tree V),
    k1 <> k2 ->
    lookup d k' (insertTree k1 v1 (insertTree k2 v2 t))
    = lookup d k' (insertTree k2 v2 (insertTree k1 v1 t)).
Proof.
  intros. induction t.
  - simpl. bdall.
  - simpl. bdall.
Qed.

(** [] *)

(** Our ability to prove these lemmas without reference to the
    underlying tree implementation demonstrates they hold for any map
    implementation that satisfies the three basic equations. *)

(** Each of these lemmas just proved was phrased as an equality
    between the results of looking up an arbitrary key [k'] in two
    maps.  But the lemmas for the function-based maps were phrased as
    direct equalities between the maps themselves.

    Could we state the tree lemmas with direct equalities?  For
    [insert_shadow], the answer is yes: *)

Lemma insert_shadow_equality : forall (V : Type) (t : tree V) (k : key) (v v' : V),
    insertTree k v (insertTree k v' t) = insertTree k v t.
Proof.
  induction t; intros; bdall.
  - rewrite IHt1; auto.
  - rewrite IHt2; auto.
Qed.

(** But the other two direct equalities on BSTs do not necessarily
    hold. *)

(** **** Exercise: 2 stars, standard, optional (direct_equalities_break) *)

(** Prove that the other equalities do not hold.  Hint: find a counterexample
    first on paper, then use the [exists] tactic to instantiate the theorem
    on your counterexample.  The simpler your counterexample, the simpler
    the rest of the proof will be. *)

Lemma insert_same_equality_breaks :
  exists (V : Type) (d : V) (t : tree V) (k : key),
      insertTree k (lookup d k t) t <> t.
Proof.
  exists nat, 0, E, 1.
  unfold insertTree, lookup.
  simpl.
  unfold not. intros H.
  inversion H.
Qed.

Lemma insert_permute_equality_breaks :
  exists (V : Type) (v1 v2 : V) (k1 k2 : key) (t : tree V),
    k1 <> k2 /\ insertTree k1 v1 (insertTree k2 v2 t) <> insertTree k2 v2 (insertTree k1 v1 t).
Proof.
  exists nat, 1, 2, 1, 2, E.
  split.
  - intros H. inversion H.
  - unfold insertTree, lookup. simpl. unfold not. intros H. discriminate H.
Qed.

(** [] *)

(* ################################################################# *)
(** * Converting a BST to a List *)

(** Let's add a new operation to our BST: converting it to an
    _association list_ that contains the key--value bindings from the
    tree stored as pairs.  If that list is sorted by the keys, then
    any two trees that represent the same map would be converted to
    the same list. Here's a function that does so with an in-order
    traversal of the tree: *)

Fixpoint elements {V : Type} (t : tree V) : list (key * V) :=
  match t with
  | E => []
  | T l k v r => elements l ++ [(k, v)] ++ elements r
  end.

Example elements_ex :
    elements ex_tree = [(2, "two"); (4, "four"); (5, "five")]%string.
Proof. reflexivity. Qed.

(** Here are three desirable properties for [elements]:

    1. The list has the same bindings as the tree.

    2. The list is sorted by keys.

    3. The list contains no duplicate keys.

    Let's formally specify and verify them. *)

(* ================================================================= *)
(** ** Part 1: Same Bindings *)

(** We want to show that a binding is in [elements t] iff it's in
    [t]. We'll prove the two directions of that bi-implication
    separately:

    - [elements] is _complete_: if a binding is in [t] then it's in
      [elements t].

    - [elements] is _correct_: if a binding is in [elements t] then
      it's in [t].  *)

(** Getting the specification of completeness right is a little
    tricky.  It's tempting to start off with something too simple like
    this: *)

Definition elements_complete_broken_spec :=
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    lookup d k t = v ->
    In (k, v) (elements t).

(** The problem with that specification is how it handles the default
    element [d]: the specification would incorrectly require [elements
    t] to contain a binding [(k, d)] for all keys [k] unbound in
    [t]. That would force [elements t] to be infinitely long, since
    it would have to contain a binding for every natural number. We can
    observe this problem right away if we begin the proof: *)

Theorem elements_complete_broken : elements_complete_broken_spec.
Proof.
  unfold elements_complete_broken_spec. intros. induction t.
  - (* t = E *) simpl.
    (** We have nothing to work with, since [elements E] is [[]]. *)
Abort.

(** The solution is to check first to see whether [k] is bound in [t].
    Only bound keys need be in the list of elements: *)

Definition elements_complete_spec :=
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    bound k t = true ->
    lookup d k t = v ->
    In (k, v) (elements t).

(** **** Exercise: 3 stars, standard (elements_complete) *)

(** Prove that [elements] is complete. Proceed by induction on [t]. *)

Theorem elements_complete : elements_complete_spec.
Proof.
  intros V k v d t.
  induction t as [|l IHl x vx r IHr].
  - simpl. intro bound. discriminate.
  - intros H_bound H_lookup.
    simpl in *. unfold bound in H_bound. unfold lookup in H_lookup.
    simpl in *. bdestruct (k <? x).
    + apply in_or_app. left.
      apply IHl; try assumption.
    + bdestruct (k >? x).
      *  apply in_or_app; right. simpl. right. apply IHr; assumption. 
      * apply in_or_app; right. simpl. left. rewrite H_lookup. assert (k = x). { try lia. }
        rewrite H1. reflexivity.
Qed.

(** [] *)

(** The specification for correctness likewise mentions that the
    key must be bound: *)

Definition elements_correct_spec :=
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (elements t) ->
    bound k t = true /\ lookup d k t = v.

(** Proving correctness requires more work than completeness.

    [BST] uses [ForallT] to say that all nodes in the left/right
    subtree have smaller/greater keys than the root.  We need to
    relate [ForallT], which expresses that all nodes satisfy a
    property, to [Forall], which expresses that all list elements
    satisfy a property.

    The standard library contains a helpful lemma about [Forall]: *)

Check Forall_app.

(** **** Exercise: 2 stars, standard (elements_preserves_forall) *)

(** Prove that if a property [P] holds of every node in a tree [t],
    then that property holds of every pair in [elements t]. Proceed
    by induction on [t].

    There is a little mismatch between the type of [P] in [ForallT]
    and the type of the property accepted by [Forall], so we have to
    _uncurry_ [P] when we pass it to [Forall]. (See [Poly] for
    more about uncurrying.) The single quote used below is the Coq
    syntax for doing a pattern match in the function arguments. *)

Definition uncurry {X Y Z : Type} (f : X -> Y -> Z) '(a, b) :=
  f a b.

Hint Transparent uncurry : core.

Lemma elements_preserves_forall : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t ->
    Forall (uncurry P) (elements t).
Proof.
  intros V P t H.
  induction t as [| l IHl k v r IHr].
  - simpl. constructor.
  - simpl. apply Forall_app. split.
    + apply IHl. inversion H; subst. destruct H1. assumption.
    + constructor.
      * simpl. unfold uncurry. inversion H. apply H0.
      * apply IHr. inversion H; subst. destruct H1. apply H2.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (elements_preserves_relation) *)

(** Prove that if all the keys in [t] are in a relation [R] with a
    distinguished key [k'], then any key [k] in [elements t] is also
    related by [R] to [k']. For example, [R] could be [<], in which
    case the lemma says that if all the keys in [t] are less than
    [k'], then all the keys in [elements t] are also less than
    [k'].

    Hint: you don't need induction.  Immediately look for a way
    to use [elements_preserves_forall] and library theorem
    [Forall_forall]. *)

Lemma elements_preserves_relation :
  forall (V : Type) (k k' : key) (v : V) (t : tree V) (R : key -> key -> Prop),
    ForallT (fun y _ => R y k') t
    -> In (k, v) (elements t)
    -> R k k'.
Proof.
  intros V k k' v t R H InElem.
  apply elements_preserves_forall with (P := fun y _ => R y k') in H.
  rewrite Forall_forall in H.
  apply H in InElem.
  simpl in InElem.
  apply InElem.
Qed.

(** [] *)

(** **** Exercise: 4 stars, standard (elements_correct) *)

(** Prove that [elements] is correct. Proceed by induction on the
    evidence that [t] is a BST. *)

Theorem elements_correct : elements_correct_spec.
Proof.
  unfold elements_correct_spec.
  intros V k v d t H_BST H_in.
  induction H_BST as [|l IHl x vx r IHr].
  - simpl in H_in. contradiction.
  - simpl in H_in.
    apply in_app_or in H_in.
    destruct H_in as [Hin_l | Hin_rv]; simpl.
    + apply IHH_BST1 in Hin_l; auto. destruct Hin_l as [Hbound Hlookup]. split; auto.
      * simpl. bdall. destruct IHH_BST2. Admitted.

(** [] *)

(** The inverses of completeness and correctness also should hold:

    - inverse completeness: if a binding is not in [t] then it's not
      in [elements t].

    - inverse correctness: if a binding is not in [elements t] then
      it's not in [t]. *)

(* Let's prove that they do. *)

(** **** Exercise: 2 stars, advanced (elements_complete_inverse) *)

(** This inverse doesn't require induction.  Look for a way to use
    [elements_correct] to quickly prove the result. *)

Theorem elements_complete_inverse :
  forall (V : Type) (k : key) (v : V) (t : tree V),
    BST t ->
    bound k t = false ->
    ~ In (k, v) (elements t).
Proof.
  intros V k v t H_BST H_unbound.
  unfold not; intros H_in.
  apply elements_correct in H_in; auto.
  rewrite H_in in H_unbound. discriminate H_unbound.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (elements_correct_inverse) *)

(** Prove the inverse.  First, prove this helper lemma by induction on
    [t]. *)

Lemma bound_value : forall (V : Type) (k : key) (t : tree V),
    bound k t = true -> exists v, forall d, lookup d k t = v.
Proof.
  intros V k t.
  induction t as [|l IHl x vx r IHr]; intros H_bound; simpl in H_bound.
  - discriminate H_bound.
  - bdestruct (k <? x).
    + bdall.
    + bdestruct (k >? x).
      * bdall.
      * exists vx. intros d. simpl. bdall.
Qed.

(** Prove the main result.  You don't need induction. *)

Theorem elements_correct_inverse :
  forall (V : Type) (k : key) (t : tree V),
    (forall v, ~ In (k, v) (elements t)) ->
    bound k t = false.
Proof.
  intros V k t H.
  destruct (bound k t) eqn:H_bound; auto.
  apply bound_value in H_bound. destruct H_bound as [v H_lookup].
  assert (H_in: In (k, v) (elements t)).
   { unfold not in H. Abort.
(** [] *)

(* ================================================================= *)
(** ** Part 2: Sorted (Advanced) *)

(** We want to show that [elements] is sorted by keys.  We follow a
    proof technique contributed by Lydia Symmons et al.*)

(** **** Exercise: 3 stars, advanced (sorted_app) *)

(** Prove that inserting an intermediate value between two lists
    maintains sortedness. Proceed by induction on the evidence
    that [l1] is sorted. *)

Lemma sorted_app: forall l1 l2 x,
  sorted l1 -> sorted l2 ->
  Forall (fun n => n < x) l1 -> Forall (fun n => n > x) l2 ->
  sorted (l1 ++ x :: l2).
Proof.
    intros l1 l2 x Hsorted1 Hsorted2 Hforall1 Hforall2.
  induction Hsorted1 as [| | h1 l1 Hsorted1 IH1 Hle1].
  - simpl. Admitted.

(** [] *)

(** **** Exercise: 4 stars, advanced (sorted_elements) *)

(** The keys in an association list are the first elements of every
    pair: *)

Definition list_keys {V : Type} (lst : list (key * V)) :=
  map fst lst.

(** Prove that [elements t] is sorted by keys. Proceed by induction
    on the evidence that [t] is a BST. *)

Theorem sorted_elements : forall (V : Type) (t : tree V),
    BST t -> sorted (list_keys (elements t)).
Proof.
  intros V t H_bst. induction H_bst.
  - simpl. constructor.
  - simpl. Admitted.


(** [] *)

(* ================================================================= *)
(** ** Part 3: No Duplicates (Advanced and Optional) *)

(** We want to show that [elements t] contains no duplicate
    key bindings. Tree [t] itself cannot contain any duplicates, so the
    list that [elements] produces shouldn't either. The standard
    library already contains a helpful inductive proposition,
    [NoDup]. *)

Print NoDup.

(** The library is missing a theorem, though, about [NoDup] and [++].
    To state that theorem, we first need to formalize what it means
    for two lists to be disjoint: *)

Definition disjoint {X:Type} (l1 l2: list X) := forall (x : X),
    In x l1 -> ~ In x l2.

(** **** Exercise: 3 stars, advanced, optional (NoDup_append) *)

(** Prove that if two lists are disjoint, appending them preserves
    [NoDup].  Hint: You might already have proved this theorem in an
    advanced exercise in [IndProp]. *)

Lemma NoDup_append : forall (X:Type) (l1 l2: list X),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 ->
  NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 H_nodup_l1 H_nodup_l2 H_disjoint.
  induction H_nodup_l1 as [| x l1' H_not_in_l1' H_nodup_l1' IH].
  - simpl. assumption.
  - simpl. constructor.
    + intro H_in. apply in_app_or in H_in. destruct H_in as [H_in_l1' | H_in_l2].
      * contradiction.
      * apply (H_disjoint x). left. reflexivity. assumption.
    + apply IH. intros y H_in_l1'. apply (H_disjoint y). right. assumption.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (elements_nodup_keys) *)

(** Prove that there are no duplicate keys in the list returned
    by [elements]. Proceed by induction on the evidence that [t] is a
    BST. Make use of library theorems about [map] as needed. *)

Theorem elements_nodup_keys : forall (V : Type) (t : tree V),
    BST t ->
    NoDup (list_keys (elements t)).
Proof.
  intros V t H_bst. induction H_bst.
  - simpl. constructor.
  - simpl. Admitted.

(** [] *)

(** That concludes the proof of correctness of [elements]. *)

(* ################################################################# *)
(** * A Faster [elements] Implementation *)

(** The implemention of [elements] is inefficient because of how
    it uses the [++] operator.  On a balanced tree its running time is
    linearithmic, because it does a linear number of concatentations
    at each level of the tree. On an unbalanced tree it's quadratic
    time.  Here's a tail-recursive implementation than runs in linear
    time, regardless of whether the tree is balanced: *)

Fixpoint fast_elements_tr {V : Type} (t : tree V)
         (acc : list (key * V)) : list (key * V) :=
  match t with
  | E => acc
  | T l k v r => fast_elements_tr l ((k, v) :: fast_elements_tr r acc)
  end.

Definition fast_elements {V : Type} (t : tree V) : list (key * V) :=
  fast_elements_tr t [].

(** **** Exercise: 3 stars, standard (fast_elements_eq_elements) *)

(** Prove that [fast_elements] and [elements] compute the same
    function. *)

Lemma fast_elements_tr_helper :
  forall (V : Type) (t : tree V) (lst : list (key * V)),
    fast_elements_tr t lst = elements t ++ lst.
Proof.
  induction t as [| l IHl k v r IHr].
  - simpl. reflexivity.
  - simpl.
    intros.
    rewrite IHr.
    rewrite IHl.
    rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma fast_elements_eq_elements : forall (V : Type) (t : tree V),
    fast_elements t = elements t.
Proof.
  intros V t.
  unfold fast_elements.
  rewrite fast_elements_tr_helper.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

(** [] *)

(** Since the two implementations compute the same function, all
    the results we proved about the correctness of [elements]
    also hold for [fast_elements].  For example: *)

Corollary fast_elements_correct :
  forall (V : Type) (k : key) (v d : V) (t : tree V),
    BST t ->
    In (k, v) (fast_elements t) ->
    bound k t = true /\ lookup d k t = v.
Proof.
  intros. rewrite fast_elements_eq_elements in *.
  apply elements_correct; assumption.
Qed.

(** This corollary illustrates a general technique:  prove the correctness
    of a simple, slow implementation; then prove that the slow version
    is functionally equivalent to a fast implementation.  The proof of
    correctness for the fast implementation then comes "for free". *)

(* ################################################################# *)
(** * An Algebraic Specification of [elements] *)

(** The verification of [elements] we did above did not adhere to the
    algebraic specification approach, which would suggest that we look
    for equations of the form

      elements empty_tree = ...
      elements (insert k v t) = ... (elements t) ...

    The first of these is easy; we can trivially prove the following:
    *)

Lemma elements_empty : forall (V : Type),
    @elements V empty_tree = [].
Proof.
  intros. simpl. reflexivity.
Qed.

(** But for the second equation, we have to express the result of
    inserting [(k, v)] into the elements list for [t], accounting for
    ordering and the possibility that [t] may already contain a pair
    [(k, v')] which must be replaced.  The following rather ugly
    function will do the trick: *)

Fixpoint kvs_insert {V : Type} (k : key) (v : V) (kvs : list (key * V)) :=
  match kvs with
  | [] => [(k, v)]
  | (k', v') :: kvs' =>
    if k <? k' then (k, v) :: kvs
    else if k >? k' then (k', v') :: kvs_insert k v kvs'
         else (k, v) :: kvs'
  end.

(** That's not satisfactory, because the definition of
    [kvs_insert] is so complex. Moreover, this equation doesn't tell
    us anything directly about the overall properties of [elements t]
    for a given tree [t].  Nonetheless, we can proceed with a rather
    ugly verification. *)

(** **** Exercise: 3 stars, standard, optional (kvs_insert_split) *)
Lemma kvs_insert_split :
  forall (V : Type) (v v0 : V) (e1 e2 : list (key * V)) (k k0 : key),
    Forall (fun '(k',_) => k' < k0) e1 ->
    Forall (fun '(k',_) => k' > k0) e2 ->
    kvs_insert k v (e1 ++ (k0,v0):: e2) =
    if k <? k0 then
      (kvs_insert k v e1) ++ (k0,v0)::e2
    else if k >? k0 then
           e1 ++ (k0,v0)::(kvs_insert k v e2)
         else
           e1 ++ (k,v)::e2.
Proof.
 intros V v v0 e1 e2 k k0 H_lt H_gt.
  induction e1 as [| (k', v') e1' IH].
  - simpl. destruct (k <? k0) eqn:Hk_lt.
    + reflexivity.
    + destruct (k >? k0) eqn:Hk_gt.
      * reflexivity.
      * reflexivity.
  - simpl. destruct (k <? k') eqn:Hk_lt'.
    + simpl. bdall.
      * Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (kvs_insert_elements) *)
Lemma kvs_insert_elements : forall (V : Type) (t : tree V),
    BST t ->
    forall (k : key) (v : V),
      elements (insertTree k v t) = kvs_insert k v (elements t).
Proof.
   intros V t H_bst. induction H_bst as [| l x v' r H_l H_r H_bst_l H_bst_r IH_l IH_r].
  - intros k v. simpl. reflexivity.
  - intros k v.
    simpl.
    destruct (k <? x) eqn:Hk_lt.
    + Admitted.
(** [] *)

(* ################################################################# *)
(** * Model-based Specifications *)

(** At the outset, we mentioned studying two techniques for
    specifying the correctness of BST operations in this chapter.  The
    first was algebraic specification.

    Another approach to proving correctness of search trees is to
    relate them to our existing implementation of functional partial
    maps, as developed in [Maps]. To prove the correctness of a
    search-tree algorithm, we can prove:

    - Any search tree corresponds to some functional partial map,
      using a function or relation that we write down.

    - The [lookup] operation on trees gives the same result as the
      [find] operation on the corresponding map.

    - Given a tree and corresponding map, if we [insert] on the tree
      and [update] the map with the same key and value, the resulting
      tree and map are in correspondence.

    This approach is sometimes called _model-based specification_: we
    show that our implementation of a data type corresponds to a more
    more abstract _model_ type that we already understand. To reason
    about programs that use the implementation, it suffices to reason
    about the behavior of the abstract type, which may be
    significantly easier.  For example, we can take advantage of laws
    that we proved for the abstract type, like [update_eq] for
    functional maps, without having to prove them again for the
    concrete tree type.

    We also need to be careful here, because the type of functional
    maps as defined in [Maps] do not actually behave quite like
    our tree-based maps. For one thing, functional maps can be defined
    on an infinite number of keys, and there is no mechanism for
    enumerating over the key set. To maintain correspondence with our
    finite trees, we need to make sure that we consider only
    functional maps built by finitely many applications of constructor
    functions ([empty] and [update]). Also, thanks to functional
    extensionality, functional maps obey stronger equality laws than
    our trees do (as we investigated in the [direct_equalities]
    exercise above), so we should not be misled into thinking that
    every fact we can prove about abstract maps necessarily holds for
    concrete ones.

    Compared to the algebraic-specification approach described earlier
    in this chapter, the model-based approach can save some proof
    effort, especially if we already have a well-developed theory for
    the abstract model type.  On the other hand, we have to give an
    explicit _abstraction_ relation between trees and maps, and show
    that it is maintained by all operations. In the end, about the
    same amount of work is needed to show correctness, though the work
    shows up in different places depending on how the abstraction
    relation is defined. *)

(** We now give a model-based specification for trees in terms
    of functional partial maps. It is based on a simple abstraction
    relation that builds a functional map element by element. *)

Fixpoint map_of_list {V : Type} (el : list (key * V)) : partial_map V :=
  match el with
  | [] => empty
  | (k, v) :: el' => update (map_of_list el') k v
  end.

Definition Abs {V : Type} (t : tree V) : partial_map V :=
  map_of_list (elements t).

(** In general, model-based specifications may use an abstraction
    relation, allowing each concrete value to be related to multiple
    abstract values.  But in this case a simple abstraction _function_
    will do, assigning a unique abstract value to each concrete
    one. *)

(** One difference between trees and functional maps is that
    applying the latter returns an [option V] which might be [None],
    whereas [lookup] returns a default value if key is not bound
    lookup fails.  We can easily provide a function on functional
    partial maps having the latter behavior. *)

Definition find {V : Type} (d : V) (k : key) (m : partial_map V) : V :=
  match m k with
  | Some v => v
  | None => d
  end.

(** We also need a [bound] operation on maps. *)

Definition map_bound {V : Type} (k : key) (m : partial_map V) : bool :=
  match m k with
  | Some _ => true
  | None => false
  end.

(** We now prove that each operation preserves (or establishes)
    the abstraction function.

    concrete        abstract
    --------        --------
    empty_tree      empty
    bound           map_bound
    lookup          find
    insert          update
*)

(** The following lemmas will be useful, though you are not required
    to prove them. They can all be proved by induction on the list. *)

(** **** Exercise: 2 stars, standard, optional (in_fst) *)
Lemma in_fst : forall (X Y : Type) (lst : list (X * Y)) (x : X) (y : Y),
    In (x, y) lst -> In x (map fst lst).
Proof.
  intros X Y lst x y H_in.
  induction lst as [| (x', y') lst' IH].
  - simpl in H_in. contradiction.
  - simpl in H_in. simpl. destruct H_in as [H_eq | H_in'].
    + inversion H_eq. left. reflexivity.
    + right. apply IH. assumption.
Qed.

(** **** Exercise: 2 stars, standard, optional (in_map_of_list) *)
Lemma in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key) (v : V),
    NoDup (map fst el) ->
    In (k,v) el -> (map_of_list el) k = Some v.
Proof.
  intros V el k v H_nodup H_in.
  induction el as [| (k', v') el' IH].
  - simpl in H_in. contradiction.
  - simpl in H_nodup. inversion H_nodup as [| k'' el'' HNotIn HNoDup']. subst.
    simpl in H_in. destruct H_in as [Hkv | HIn'].
    + inversion Hkv. subst. simpl. unfold not in HNotIn. Admitted.

(** **** Exercise: 2 stars, standard, optional (not_in_map_of_list) *)
Lemma not_in_map_of_list : forall (V : Type) (el : list (key * V)) (k : key),
    ~ In k (map fst el) -> (map_of_list el) k = None.
Proof.
  intros V el k Hnotin.
  induction el as [| [k' v'] el' IH].
  - reflexivity.
  - simpl in Hnotin. simpl. unfold not in Hnotin. unfold not in IH. Admitted.

Lemma empty_relate : forall (V : Type),
    @Abs V empty_tree = empty.
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, optional (bound_relate) *)

Theorem bound_relate : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    map_bound k (Abs t) = bound k t.
Proof.
  intros.
  induction t as [| l k' v r IHl IHr].
  - reflexivity.
  - simpl. inversion H; subst. Admitted. 

(** [] *)

(** **** Exercise: 3 stars, standard, optional (lookup_relate) *)

Lemma lookup_relate : forall (V : Type) (t : tree V) (d : V) (k : key),
    BST t -> find d k (Abs t) = lookup d k t.
Proof.
  intros V t d k Hbst.
  induction t as [| l k' v r IHl IHr].
  - reflexivity.
  - simpl in Hbst. simpl.
    inversion Hbst; subst. Admitted.

(** **** Exercise: 3 stars, standard, optional (insert_relate) *)
Lemma insert_relate : forall (V : Type) (t : tree V) (k : key) (v : V),
  BST t -> Abs (insertTree k v t) = update (Abs t) k v.
Proof.
  (* TODO: find a direct proof that doesn't rely on [kvs_insert_elements] *)
    unfold Abs.
  intros.
  rewrite kvs_insert_elements; auto.
  remember (elements t) as l.
  clear -l. (* clear everything not about [l] *)
   induction l as [| [k' v'] l' IH].
  - simpl. reflexivity.
  - simpl. Admitted.
(** [] *)

(** The previous three lemmas are in essence saying that the following
    diagrams commute.

             bound k
      t -------------------+
      |                    |
  Abs |                    |
      V                    V
      m -----------------> b
           map_bound k

            lookup d k
      t -----------------> v
      |                    |
  Abs |                    | Some
      V                    V
      m -----------------> Some v
             find d k

            insert k v
      t -----------------> t'
      |                    |
  Abs |                    | Abs
      V                    V
      m -----------------> m'
            update' k v

    Where we define:

      update' k v m = update m k v

*)

(** Functional partial maps lack a way to extract or iterate
    over their elements, so we cannot give an analogous abstract
    operation for [elements]. Instead, we can prove this trivial
    little lemma. *)

Lemma elements_relate : forall (V : Type) (t : tree V),
  BST t ->
  map_of_list (elements t) = Abs t.
Proof.
  unfold Abs. intros. reflexivity.
Qed.

(* ################################################################# *)
(** * An Alternative Abstraction Relation (Optional, Advanced) *)

(** There is often more than one way to specify a suitable abstraction
    relation between given concrete and abstract datatypes. The
    following exercises explore another way to relate search trees to
    functional partial maps without using [elements] as an
    intermediate step.

    We extend our definition of functional partial maps by adding a
    new primitive for combining two partial maps, which we call
    [union].  Our intention is that it only be used to combine maps
    with disjoint key sets; to keep the operation symmetric, we make
    the result be undefined on any key they have in common.  *)

Definition union {X} (m1 m2: partial_map X) : partial_map X :=
  fun k =>
    match (m1 k, m2 k) with
    | (None, None) => None
    | (None, Some v) => Some v
    | (Some v, None) => Some v
    | (Some _, Some _) => None
    end.

(** We can prove some simple properties of lookup and update on unions,
    which will prove useful later. *)

(** **** Exercise: 2 stars, standard, optional (union_collapse) *)
Lemma union_left : forall {X} (m1 m2: partial_map X) k,
    m2 k = None -> union m1 m2 k = m1 k.
Proof.
  intros X m1 m2 k Hnone.
  unfold union. rewrite Hnone.
  destruct (m1 k); reflexivity.
Qed.

Lemma union_right : forall {X} (m1 m2: partial_map X) k,
    m1 k = None ->
    union m1 m2 k = m2 k.
Proof.
  intros X m1 m2 k Hnone.
  unfold union. rewrite Hnone.
  destruct (m2 k); reflexivity.
Qed.

Lemma union_both : forall {X} (m1 m2 : partial_map X) k v1 v2,
    m1 k = Some v1 ->
    m2 k = Some v2 ->
    union m1 m2 k = None.
Proof.
  intros X m1 m2 k v1 v2 Hm1 Hm2.
  unfold union. rewrite Hm1, Hm2. reflexivity.
Qed.

(** **** Exercise: 3 stars, standard, optional (union_update) *)
Lemma union_update_right : forall {X} (m1 m2: partial_map X) k v,
    m1 k = None ->
    update (union m1 m2) k v = union m1 (update m2 k v).
Proof.
  intros X m1 m2 k v Hnone.
  unfold union, update. extensionality x.
  Admitted.

Lemma union_update_left : forall {X} (m1 m2: partial_map X) k v,
    m2 k = None ->
    update (union m1 m2) k v = union (update m1 k v) m2.
Proof.
  intros X m1 m2 k v Hnone.
  unfold union, update. extensionality x.
  Admitted.

(** We can now write a direct conversion function from trees to maps
    based on the structure of the tree, and prove a basic property
    preservation result. *)

Fixpoint map_of_tree {V : Type} (t: tree V) : partial_map V :=
  match t with
  | E => empty
  | T l k v r => update (union (map_of_tree l) (map_of_tree r)) k v
  end.

(** **** Exercise: 3 stars, advanced, optional (map_of_tree_prop) *)
Lemma map_of_tree_prop : forall (V : Type) (P : key -> V -> Prop) (t : tree V),
    ForallT P t ->
    forall k v, (map_of_tree t) k = Some v ->
           P k v.
Proof.
  intros V P t Hforall k v Hmap.
  induction t as [| l k' v' r IHl IHr].
  - simpl in Hmap. discriminate.
  - simpl in Hmap. inversion Hforall as [Hl [Hr Hroot]].
    apply IHr. -- apply Hroot. -- Admitted.

(** Finally, we define our new abstraction function, and prove the
    same lemmas as before. *)

Definition Abs' {V : Type} (t: tree V) : partial_map V :=
  map_of_tree t.

Lemma empty_relate' : forall (V : Type),
    @Abs' V empty_tree = empty.
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced, optional (bound_relate') *)
Theorem bound_relate' : forall (V : Type) (t : tree V) (k : key),
    BST t ->
    map_bound k (Abs' t) = bound k t.
Proof.
  intros V t k Hbst.
  induction t as [| l k' v' r IHl IHr].
  - simpl. reflexivity.
  - simpl in Hbst. inversion Hbst; subst.
    simpl. unfold map_bound.
Admitted.

(** **** Exercise: 3 stars, advanced, optional (lookup_relate') *)
Lemma lookup_relate' : forall (V : Type) (d : V) (t : tree V) (k : key),
    BST t -> find d k (Abs' t) = lookup d k t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (insert_relate') *)
Lemma insert_relate' : forall (V : Type) (k : key) (v : V) (t : tree V),
   BST t -> Abs' (insertTree k v t) = update (Abs' t) k v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The [elements_relate] lemma, which was trivial for our previous [Abs]
    function, is considerably harder this time.  We suggest starting with
    an auxiliary lemma. *)

(** **** Exercise: 3 stars, advanced, optional (map_of_list_app) *)
Lemma map_of_list_app : forall (V : Type) (el1 el2: list (key * V)),
   disjoint (map fst el1) (map fst el2) ->
   map_of_list (el1 ++ el2) = union (map_of_list el1) (map_of_list el2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (elements_relate') *)
Lemma elements_relate' : forall (V : Type) (t : tree V),
  BST t ->
  map_of_list (elements t) = Abs' t.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Efficiency of Search Trees *)

(** All the theory we've developed so far has been about
    correctness.  But the reason we use binary search trees is that
    they are efficient.  That is, if there are [N] elements in a
    (reasonably well balanced) BST, each insertion or lookup takes
    about [log N] time.

    What could go wrong? *)

(**  1. The search tree might not be balanced.  In that case, each
        insertion or lookup will take as much as linear time.

        - SOLUTION: use an algorithm that ensures the trees stay
          balanced.  We'll do that in [Redblack]. *)

(**   2. Our keys are natural numbers, and Coq's [nat] type takes linear
        time per comparison.  That is, computing (j <? k) takes time
        proportional to the value of [k-j].

        - SOLUTION: represent keys by a data type that has a more
          efficient comparison operator.  We used [nat] in this chapter
          because it's something easy to work with. *)

(**   3. There's no notion of running time in Coq.  That is, we can't
        say what it means that a Coq function "takes N steps to
        evaluate."  Therefore, we can't prove that binary search trees
        are efficient.

        - SOLUTION 1: Don't prove (in Coq) that they're efficient;
          just prove that they are correct.  Prove things about their
          efficiency the old-fashioned way, on pencil and paper.

        - SOLUTION 2: Prove in Coq some facts about the height of the
          trees, which have direct bearing on their efficiency.  We'll
          explore that in [Redblack].

        - SOLUTION 3: Apply bleeding-edge frameworks for reasoning
          about run-time of programs represented in Coq. *)

(**   4. Our functions in Coq are models of implementations in "real"
         programming languages.  What if the real implementations
         differ from the Coq models?

         - SOLUTION: Use Coq's [extraction] feature to derive the real
	   implementation (in Ocaml or Haskell) automatically from the
	   Coq function.  Or, use Coq's [Compute] or [Eval
	   native_compute] feature to compile and run the programs
	   efficiently inside Coq.  We'll explore [extraction] in
	   [Extract]. *)

(* 2024-08-25 08:38 *)