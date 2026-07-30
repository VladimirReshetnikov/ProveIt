(**
  Formulas intrinsically sorted by the arithmetical hierarchy.

  This ports the representation and structural core of
  [Foundation/FirstOrder/Arithmetic/Definability/Hierarchy.lean].  The Coq
  API keeps the hierarchy certificate in [Type], so constructors and rewrites
  carry their proof obligations directly and require no proof-to-data choice.
*)

From Foundation.Syntax.Predicate Require Import Language Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Hierarchy.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive arithmetic_hierarchy_class : Type :=
| ArithmeticHierarchySigma
| ArithmeticHierarchyPi
| ArithmeticHierarchyDelta.

Record arithmetic_hierarchy_symbol : Type := {
  arithmetic_hierarchy_symbol_class : arithmetic_hierarchy_class;
  arithmetic_hierarchy_symbol_rank : nat
}.

Definition arithmetic_sigma_symbol (rank : nat) : arithmetic_hierarchy_symbol :=
  {| arithmetic_hierarchy_symbol_class := ArithmeticHierarchySigma;
     arithmetic_hierarchy_symbol_rank := rank |}.

Definition arithmetic_pi_symbol (rank : nat) : arithmetic_hierarchy_symbol :=
  {| arithmetic_hierarchy_symbol_class := ArithmeticHierarchyPi;
     arithmetic_hierarchy_symbol_rank := rank |}.

Definition arithmetic_delta_symbol (rank : nat) : arithmetic_hierarchy_symbol :=
  {| arithmetic_hierarchy_symbol_class := ArithmeticHierarchyDelta;
     arithmetic_hierarchy_symbol_rank := rank |}.

Definition arithmetic_sigma_zero_symbol := arithmetic_sigma_symbol 0.
Definition arithmetic_pi_zero_symbol := arithmetic_pi_symbol 0.
Definition arithmetic_delta_zero_symbol := arithmetic_delta_symbol 0.
Definition arithmetic_sigma_one_symbol := arithmetic_sigma_symbol 1.
Definition arithmetic_pi_one_symbol := arithmetic_pi_symbol 1.
Definition arithmetic_delta_one_symbol := arithmetic_delta_symbol 1.

Record arithmetic_sorted_polar_formula (X : Type) (n : nat)
    (pol : bool) (rank : nat) : Type := {
  arithmetic_sorted_polar_val : semiformula oring_language X n;
  arithmetic_sorted_polar_prop :
    arithmetic_hierarchy X pol rank n arithmetic_sorted_polar_val
}.

Arguments arithmetic_sorted_polar_val {X n pol rank} _.
Arguments arithmetic_sorted_polar_prop {X n pol rank} _.

Definition arithmetic_sorted_formula_by (X : Type) (n : nat)
    (class : arithmetic_hierarchy_class) (rank : nat) : Type :=
  match class with
  | ArithmeticHierarchySigma =>
      arithmetic_sorted_polar_formula X n arithmetic_sigma rank
  | ArithmeticHierarchyPi =>
      arithmetic_sorted_polar_formula X n arithmetic_pi rank
  | ArithmeticHierarchyDelta =>
      (arithmetic_sorted_polar_formula X n arithmetic_sigma rank *
       arithmetic_sorted_polar_formula X n arithmetic_pi rank)%type
  end.

Definition arithmetic_sorted_formula (X : Type) (n : nat)
    (symbol : arithmetic_hierarchy_symbol) : Type :=
  arithmetic_sorted_formula_by X n
    (arithmetic_hierarchy_symbol_class symbol)
    (arithmetic_hierarchy_symbol_rank symbol).

Definition ArithmeticSortedSigma {X n} rank
    (p : semiformula oring_language X n)
    (H : arithmetic_hierarchy X arithmetic_sigma rank n p) :
    arithmetic_sorted_formula X n (arithmetic_sigma_symbol rank) :=
  {| arithmetic_sorted_polar_val := p;
     arithmetic_sorted_polar_prop := H |}.

Definition ArithmeticSortedPi {X n} rank
    (p : semiformula oring_language X n)
    (H : arithmetic_hierarchy X arithmetic_pi rank n p) :
    arithmetic_sorted_formula X n (arithmetic_pi_symbol rank) :=
  {| arithmetic_sorted_polar_val := p;
     arithmetic_sorted_polar_prop := H |}.

Definition ArithmeticSortedDelta {X n} rank
    (p : arithmetic_sorted_formula X n (arithmetic_sigma_symbol rank))
    (q : arithmetic_sorted_formula X n (arithmetic_pi_symbol rank)) :
    arithmetic_sorted_formula X n (arithmetic_delta_symbol rank) :=
  (p, q).

Arguments ArithmeticSortedSigma {X n} rank p H.
Arguments ArithmeticSortedPi {X n} rank p H.
Arguments ArithmeticSortedDelta {X n} rank p q.

Definition arithmetic_sorted_formula_val {X n class rank}
    (p : arithmetic_sorted_formula_by X n class rank) :
    semiformula oring_language X n :=
  match class as c return
      arithmetic_sorted_formula_by X n c rank ->
      semiformula oring_language X n with
  | ArithmeticHierarchySigma => arithmetic_sorted_polar_val
  | ArithmeticHierarchyPi => arithmetic_sorted_polar_val
  | ArithmeticHierarchyDelta => fun q =>
      arithmetic_sorted_polar_val (fst q)
  end p.

Lemma arithmetic_sorted_sigma_prop {X n rank}
    (p : arithmetic_sorted_formula X n (arithmetic_sigma_symbol rank)) :
    arithmetic_hierarchy X arithmetic_sigma rank n
      (arithmetic_sorted_formula_val p).
Proof. exact (arithmetic_sorted_polar_prop p). Qed.

Lemma arithmetic_sorted_pi_prop {X n rank}
    (p : arithmetic_sorted_formula X n (arithmetic_pi_symbol rank)) :
    arithmetic_hierarchy X arithmetic_pi rank n
      (arithmetic_sorted_formula_val p).
Proof. exact (arithmetic_sorted_polar_prop p). Qed.

Definition arithmetic_sorted_delta_sigma {X n rank}
    (p : arithmetic_sorted_formula X n (arithmetic_delta_symbol rank)) :
    arithmetic_sorted_formula X n (arithmetic_sigma_symbol rank) := fst p.

Definition arithmetic_sorted_delta_pi {X n rank}
    (p : arithmetic_sorted_formula X n (arithmetic_delta_symbol rank)) :
    arithmetic_sorted_formula X n (arithmetic_pi_symbol rank) := snd p.

Lemma arithmetic_sorted_delta_sigma_val : forall X n rank
    (p : arithmetic_sorted_formula X n (arithmetic_delta_symbol rank)),
  arithmetic_sorted_formula_val (arithmetic_sorted_delta_sigma p) =
  arithmetic_sorted_formula_val p.
Proof. intros X n rank p; now destruct p. Qed.

Definition arithmetic_sorted_rewrite {X n Y m class rank}
    (w : rew oring_language X n Y m)
    (p : arithmetic_sorted_formula_by X n class rank) :
    arithmetic_sorted_formula_by Y m class rank.
Proof.
  destruct class.
  - exact (ArithmeticSortedSigma rank
      (semiformula_rewrite w (arithmetic_sorted_polar_val p))
      (arithmetic_hierarchy_rewrite (arithmetic_sorted_polar_prop p) w)).
  - exact (ArithmeticSortedPi rank
      (semiformula_rewrite w (arithmetic_sorted_polar_val p))
      (arithmetic_hierarchy_rewrite (arithmetic_sorted_polar_prop p) w)).
  - exact (ArithmeticSortedDelta rank
      (ArithmeticSortedSigma rank
        (semiformula_rewrite w
          (arithmetic_sorted_polar_val (fst p)))
        (arithmetic_hierarchy_rewrite
          (arithmetic_sorted_polar_prop (fst p)) w))
      (ArithmeticSortedPi rank
        (semiformula_rewrite w
          (arithmetic_sorted_polar_val (snd p)))
        (arithmetic_hierarchy_rewrite
          (arithmetic_sorted_polar_prop (snd p)) w))).
Defined.

Lemma arithmetic_sorted_rewrite_val : forall X n Y m symbol
    (w : rew oring_language X n Y m)
    (p : arithmetic_sorted_formula X n symbol),
  arithmetic_sorted_formula_val (arithmetic_sorted_rewrite w p) =
  semiformula_rewrite w (arithmetic_sorted_formula_val p).
Proof.
  intros X n Y m [class rank] w p. destruct class; reflexivity.
Qed.

Definition arithmetic_sorted_zero_hierarchy {X n class}
    (p : arithmetic_sorted_formula X n
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := 0 |}) :
    arithmetic_hierarchy X arithmetic_sigma 0 n
      (arithmetic_sorted_formula_val p).
Proof.
  destruct class.
  - exact (arithmetic_sorted_sigma_prop p).
  - apply (proj1 (@arithmetic_hierarchy_zero_iff X arithmetic_pi
      arithmetic_sigma n (arithmetic_sorted_formula_val p))).
    exact (arithmetic_sorted_pi_prop p).
  - exact (arithmetic_sorted_sigma_prop
      (arithmetic_sorted_delta_sigma p)).
Defined.

Definition arithmetic_sorted_of_zero {X n class}
    (p : arithmetic_sorted_formula X n
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := 0 |})
    (target : arithmetic_hierarchy_symbol) :
    arithmetic_sorted_formula X n target.
Proof.
  destruct target as [target_class rank]. destruct target_class.
  - apply (ArithmeticSortedSigma rank (arithmetic_sorted_formula_val p)).
    exact (arithmetic_hierarchy_of_zero
      (arithmetic_sorted_zero_hierarchy p) arithmetic_sigma rank).
  - apply (ArithmeticSortedPi rank (arithmetic_sorted_formula_val p)).
    exact (arithmetic_hierarchy_of_zero
      (arithmetic_sorted_zero_hierarchy p) arithmetic_pi rank).
  - apply (ArithmeticSortedDelta rank).
    + apply (ArithmeticSortedSigma rank (arithmetic_sorted_formula_val p)).
      exact (arithmetic_hierarchy_of_zero
        (arithmetic_sorted_zero_hierarchy p) arithmetic_sigma rank).
    + apply (ArithmeticSortedPi rank (arithmetic_sorted_formula_val p)).
      exact (arithmetic_hierarchy_of_zero
        (arithmetic_sorted_zero_hierarchy p) arithmetic_pi rank).
Defined.

Lemma arithmetic_sorted_of_zero_val : forall X n class
    (p : arithmetic_sorted_formula X n
      {| arithmetic_hierarchy_symbol_class := class;
         arithmetic_hierarchy_symbol_rank := 0 |}) target,
  arithmetic_sorted_formula_val (arithmetic_sorted_of_zero p target) =
  arithmetic_sorted_formula_val p.
Proof. intros X n class p [target_class rank]; now destruct target_class. Qed.

Definition arithmetic_sorted_verum {X n}
    (symbol : arithmetic_hierarchy_symbol) :
    arithmetic_sorted_formula X n symbol.
Proof.
  destruct symbol as [class rank]. destruct class.
  - exact (ArithmeticSortedSigma rank (Semiformula_verum n)
      (AH_verum arithmetic_sigma rank n)).
  - exact (ArithmeticSortedPi rank (Semiformula_verum n)
      (AH_verum arithmetic_pi rank n)).
  - exact (ArithmeticSortedDelta rank
      (ArithmeticSortedSigma rank (Semiformula_verum n)
        (AH_verum arithmetic_sigma rank n))
      (ArithmeticSortedPi rank (Semiformula_verum n)
        (AH_verum arithmetic_pi rank n))).
Defined.

Definition arithmetic_sorted_falsum {X n}
    (symbol : arithmetic_hierarchy_symbol) :
    arithmetic_sorted_formula X n symbol.
Proof.
  destruct symbol as [class rank]. destruct class.
  - exact (ArithmeticSortedSigma rank (Semiformula_falsum n)
      (AH_falsum arithmetic_sigma rank n)).
  - exact (ArithmeticSortedPi rank (Semiformula_falsum n)
      (AH_falsum arithmetic_pi rank n)).
  - exact (ArithmeticSortedDelta rank
      (ArithmeticSortedSigma rank (Semiformula_falsum n)
        (AH_falsum arithmetic_sigma rank n))
      (ArithmeticSortedPi rank (Semiformula_falsum n)
        (AH_falsum arithmetic_pi rank n))).
Defined.

Definition arithmetic_sorted_and {X n symbol}
    (p q : arithmetic_sorted_formula X n symbol) :
    arithmetic_sorted_formula X n symbol.
Proof.
  destruct symbol as [class rank]. destruct class.
  - apply (ArithmeticSortedSigma rank
      (Semiformula_and (arithmetic_sorted_formula_val p)
        (arithmetic_sorted_formula_val q))).
    now apply AH_and; apply arithmetic_sorted_sigma_prop.
  - apply (ArithmeticSortedPi rank
      (Semiformula_and (arithmetic_sorted_formula_val p)
        (arithmetic_sorted_formula_val q))).
    now apply AH_and; apply arithmetic_sorted_pi_prop.
  - apply (ArithmeticSortedDelta rank).
    + apply (ArithmeticSortedSigma rank
        (Semiformula_and
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_sigma p))
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_sigma q)))).
      now apply AH_and; apply arithmetic_sorted_sigma_prop.
    + apply (ArithmeticSortedPi rank
        (Semiformula_and
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_pi p))
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_pi q)))).
      now apply AH_and; apply arithmetic_sorted_pi_prop.
Defined.

Definition arithmetic_sorted_or {X n symbol}
    (p q : arithmetic_sorted_formula X n symbol) :
    arithmetic_sorted_formula X n symbol.
Proof.
  destruct symbol as [class rank]. destruct class.
  - apply (ArithmeticSortedSigma rank
      (Semiformula_or (arithmetic_sorted_formula_val p)
        (arithmetic_sorted_formula_val q))).
    now apply AH_or; apply arithmetic_sorted_sigma_prop.
  - apply (ArithmeticSortedPi rank
      (Semiformula_or (arithmetic_sorted_formula_val p)
        (arithmetic_sorted_formula_val q))).
    now apply AH_or; apply arithmetic_sorted_pi_prop.
  - apply (ArithmeticSortedDelta rank).
    + apply (ArithmeticSortedSigma rank
        (Semiformula_or
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_sigma p))
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_sigma q)))).
      now apply AH_or; apply arithmetic_sorted_sigma_prop.
    + apply (ArithmeticSortedPi rank
        (Semiformula_or
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_pi p))
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_pi q)))).
      now apply AH_or; apply arithmetic_sorted_pi_prop.
Defined.

Definition arithmetic_sorted_neg_delta {X n rank}
    (p : arithmetic_sorted_formula X n (arithmetic_delta_symbol rank)) :
    arithmetic_sorted_formula X n (arithmetic_delta_symbol rank) :=
  ArithmeticSortedDelta rank
    (ArithmeticSortedSigma rank
      (semiformula_neg
        (arithmetic_sorted_formula_val (arithmetic_sorted_delta_pi p)))
      (arithmetic_hierarchy_neg (arithmetic_sorted_pi_prop
        (arithmetic_sorted_delta_pi p))))
    (ArithmeticSortedPi rank
      (semiformula_neg
        (arithmetic_sorted_formula_val (arithmetic_sorted_delta_sigma p)))
      (arithmetic_hierarchy_neg (arithmetic_sorted_sigma_prop
        (arithmetic_sorted_delta_sigma p)))).

Definition arithmetic_sorted_ball {X n symbol}
    (t : semiterm oring_language X n)
    (p : arithmetic_sorted_formula X (S n) symbol) :
    arithmetic_sorted_formula X n symbol.
Proof.
  destruct symbol as [class rank]. destruct class.
  - apply (ArithmeticSortedSigma rank
      (semiformula_ball_lt arithmetic_lt_operator t
        (arithmetic_sorted_formula_val p))).
    exact (proj2 (@arithmetic_hierarchy_ball_lt_iff X arithmetic_sigma
      rank n t (arithmetic_sorted_formula_val p))
      (arithmetic_sorted_sigma_prop p)).
  - apply (ArithmeticSortedPi rank
      (semiformula_ball_lt arithmetic_lt_operator t
        (arithmetic_sorted_formula_val p))).
    exact (proj2 (@arithmetic_hierarchy_ball_lt_iff X arithmetic_pi
      rank n t (arithmetic_sorted_formula_val p))
      (arithmetic_sorted_pi_prop p)).
  - apply (ArithmeticSortedDelta rank).
    + apply (ArithmeticSortedSigma rank
        (semiformula_ball_lt arithmetic_lt_operator t
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_sigma p)))).
      exact (proj2 (@arithmetic_hierarchy_ball_lt_iff X arithmetic_sigma
        rank n t (arithmetic_sorted_formula_val
          (arithmetic_sorted_delta_sigma p)))
        (arithmetic_sorted_sigma_prop (arithmetic_sorted_delta_sigma p))).
    + apply (ArithmeticSortedPi rank
        (semiformula_ball_lt arithmetic_lt_operator t
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_pi p)))).
      exact (proj2 (@arithmetic_hierarchy_ball_lt_iff X arithmetic_pi
        rank n t (arithmetic_sorted_formula_val
          (arithmetic_sorted_delta_pi p)))
        (arithmetic_sorted_pi_prop (arithmetic_sorted_delta_pi p))).
Defined.

Definition arithmetic_sorted_bex {X n symbol}
    (t : semiterm oring_language X n)
    (p : arithmetic_sorted_formula X (S n) symbol) :
    arithmetic_sorted_formula X n symbol.
Proof.
  destruct symbol as [class rank]. destruct class.
  - apply (ArithmeticSortedSigma rank
      (semiformula_bex_lt arithmetic_lt_operator t
        (arithmetic_sorted_formula_val p))).
    exact (proj2 (@arithmetic_hierarchy_bex_lt_iff X arithmetic_sigma
      rank n t (arithmetic_sorted_formula_val p))
      (arithmetic_sorted_sigma_prop p)).
  - apply (ArithmeticSortedPi rank
      (semiformula_bex_lt arithmetic_lt_operator t
        (arithmetic_sorted_formula_val p))).
    exact (proj2 (@arithmetic_hierarchy_bex_lt_iff X arithmetic_pi
      rank n t (arithmetic_sorted_formula_val p))
      (arithmetic_sorted_pi_prop p)).
  - apply (ArithmeticSortedDelta rank).
    + apply (ArithmeticSortedSigma rank
        (semiformula_bex_lt arithmetic_lt_operator t
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_sigma p)))).
      exact (proj2 (@arithmetic_hierarchy_bex_lt_iff X arithmetic_sigma
        rank n t (arithmetic_sorted_formula_val
          (arithmetic_sorted_delta_sigma p)))
        (arithmetic_sorted_sigma_prop (arithmetic_sorted_delta_sigma p))).
    + apply (ArithmeticSortedPi rank
        (semiformula_bex_lt arithmetic_lt_operator t
          (arithmetic_sorted_formula_val (arithmetic_sorted_delta_pi p)))).
      exact (proj2 (@arithmetic_hierarchy_bex_lt_iff X arithmetic_pi
        rank n t (arithmetic_sorted_formula_val
          (arithmetic_sorted_delta_pi p)))
        (arithmetic_sorted_pi_prop (arithmetic_sorted_delta_pi p))).
Defined.

Definition arithmetic_sorted_exists {X n rank}
    (p : arithmetic_sorted_formula X (S n) (arithmetic_sigma_symbol (S rank))) :
    arithmetic_sorted_formula X n (arithmetic_sigma_symbol (S rank)) :=
  ArithmeticSortedSigma (S rank)
    (Semiformula_exists (arithmetic_sorted_formula_val p))
    (AH_exists (arithmetic_sorted_sigma_prop p)).

Definition arithmetic_sorted_all {X n rank}
    (p : arithmetic_sorted_formula X (S n) (arithmetic_pi_symbol (S rank))) :
    arithmetic_sorted_formula X n (arithmetic_pi_symbol (S rank)) :=
  ArithmeticSortedPi (S rank)
    (Semiformula_all (arithmetic_sorted_formula_val p))
    (AH_all (arithmetic_sorted_pi_prop p)).

Lemma arithmetic_sorted_verum_val : forall X n symbol,
  arithmetic_sorted_formula_val (@arithmetic_sorted_verum X n symbol) =
  Semiformula_verum n.
Proof. intros X n [class rank]; now destruct class. Qed.

Lemma arithmetic_sorted_falsum_val : forall X n symbol,
  arithmetic_sorted_formula_val (@arithmetic_sorted_falsum X n symbol) =
  Semiformula_falsum n.
Proof. intros X n [class rank]; now destruct class. Qed.

Lemma arithmetic_sorted_and_val : forall X n symbol
    (p q : arithmetic_sorted_formula X n symbol),
  arithmetic_sorted_formula_val (arithmetic_sorted_and p q) =
  Semiformula_and (arithmetic_sorted_formula_val p)
    (arithmetic_sorted_formula_val q).
Proof.
  intros X n [class rank] p q; destruct class; simpl;
    try reflexivity; now rewrite !arithmetic_sorted_delta_sigma_val.
Qed.

Lemma arithmetic_sorted_or_val : forall X n symbol
    (p q : arithmetic_sorted_formula X n symbol),
  arithmetic_sorted_formula_val (arithmetic_sorted_or p q) =
  Semiformula_or (arithmetic_sorted_formula_val p)
    (arithmetic_sorted_formula_val q).
Proof.
  intros X n [class rank] p q; destruct class; simpl;
    try reflexivity; now rewrite !arithmetic_sorted_delta_sigma_val.
Qed.

Lemma arithmetic_sorted_ball_val : forall X n symbol
    (t : semiterm oring_language X n)
    (p : arithmetic_sorted_formula X (S n) symbol),
  arithmetic_sorted_formula_val (arithmetic_sorted_ball t p) =
  semiformula_ball_lt arithmetic_lt_operator t
    (arithmetic_sorted_formula_val p).
Proof.
  intros X n [class rank] t p; destruct class; simpl;
    try reflexivity; now rewrite arithmetic_sorted_delta_sigma_val.
Qed.

Lemma arithmetic_sorted_bex_val : forall X n symbol
    (t : semiterm oring_language X n)
    (p : arithmetic_sorted_formula X (S n) symbol),
  arithmetic_sorted_formula_val (arithmetic_sorted_bex t p) =
  semiformula_bex_lt arithmetic_lt_operator t
    (arithmetic_sorted_formula_val p).
Proof.
  intros X n [class rank] t p; destruct class; simpl;
    try reflexivity; now rewrite arithmetic_sorted_delta_sigma_val.
Qed.

Lemma arithmetic_sorted_exists_val : forall X n rank
    (p : arithmetic_sorted_formula X (S n) (arithmetic_sigma_symbol (S rank))),
  arithmetic_sorted_formula_val (arithmetic_sorted_exists p) =
  Semiformula_exists (arithmetic_sorted_formula_val p).
Proof. reflexivity. Qed.

Lemma arithmetic_sorted_all_val : forall X n rank
    (p : arithmetic_sorted_formula X (S n) (arithmetic_pi_symbol (S rank))),
  arithmetic_sorted_formula_val (arithmetic_sorted_all p) =
  Semiformula_all (arithmetic_sorted_formula_val p).
Proof. reflexivity. Qed.
