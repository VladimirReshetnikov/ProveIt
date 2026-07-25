From Coq Require Import Vector.

From SyntheticComputability Require Import ArithmeticalHierarchySemantic
  Definitions EPF partial principles.
From SyntheticComputability.PostsProblem Require Import low_simple_predicates.
From SyntheticComputability.PostsTheorem Require Import TuringJump.
From TuringDegrees Require Import ComputablyEnumerable Core Jump Limit.

(** The principle written [¬¬ (¬¬Σ⁰₁)-LEM] by the upstream development,
    expanded here so this wrapper has a stable ASCII-facing name. *)
Definition double_negated_sigma1_lem : Prop :=
  forall (k : nat) (p : Vector.t nat k -> Prop),
    isΣsem 1 p -> ~ ~ definite p.

Definition solves_posts_problem
    {Part : partiality} {unit_encoding : encoding unit}
    {EPF_assm : EPF.EPF} (P : nat_set) : Prop :=
  computably_enumerable P /\
  turing_strict empty_set P /\
  turing_strict P zero_jump.

Section PostsProblem.
  Context {Part : partiality}.
  Context {unit_encoding : encoding unit}.
  Context {EPF_assm : EPF.EPF}.

  (** The raw upstream witness: it is c.e. and undecidable, and the stated
      constructive principle rules out computing the halting degree from it.
      The genuinely intermediate-degree formulation is derived below. *)
  Theorem posts_problem_conditional :
    exists P : nat_set,
      ~ decidable P /\
      computably_enumerable P /\
      ((~ ~ double_negated_sigma1_lem) ->
        ~ turing_reducible zero_jump P).
  Proof.
    destruct PostProblem_from_neg_negLPO
      as (P & Hundec & Hsemi & Hnot).
    exists P. repeat split; try assumption.
    intros Hprinciple Hzero.
    apply (Hnot Hprinciple).
    change (turing_reducible standard_halting P).
    transitivity zero_jump.
    - apply standard_halting_equiv_zero_jump.
    - exact Hzero.
  Qed.

  Corollary posts_problem_solution
      (mp : MP)
      (Hprinciple : ~ ~ double_negated_sigma1_lem) :
    exists P : nat_set, solves_posts_problem P.
  Proof.
    destruct posts_problem_conditional
      as (P & Hundec & Hce & Hnot).
    exists P. unfold solves_posts_problem.
    split; [exact Hce|]. split.
    - unfold turing_strict. split.
      + apply empty_set_least.
      + intro HPzero. apply Hundec.
        apply (proj1 (zero_degree_iff_decidable mp P)).
        split; [exact HPzero|apply empty_set_least].
    - unfold turing_strict. split.
      + now apply ce_turing_reducible_zero_jump.
      + exact (Hnot Hprinciple).
  Qed.
End PostsProblem.
