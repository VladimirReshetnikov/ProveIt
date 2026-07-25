From Coq Require Import Setoid.

From SyntheticComputability Require Import Definitions EPF SemiDec
  SemiDecidabilityFacts partial reductions.
From SyntheticComputability.PostsTheorem Require Import TuringJump.
From SyntheticComputability.TuringReducibility Require Import OracleComputability.
From TuringDegrees Require Import Core Jump.

(** In the synthetic library, [semi_decidable] is the machine-independent
    notion corresponding to a computably enumerable predicate. *)
Definition computably_enumerable (A : nat_set) : Prop := semi_decidable A.

Section CEAndTheJump.
  Context {Part : partiality}.
  Context {unit_encoding : encoding unit}.
  Context {EPF_assm : EPF.EPF}.

  Theorem ce_iff_many_one_zero_jump (A : nat_set) :
    computably_enumerable A <-> A ⪯ₘ zero_jump.
  Proof.
    unfold computably_enumerable, zero_jump, turing_jump.
    rewrite <- red_m_iff_semidec_jump.
    split.
    - apply semi_decidable_OracleSemiDecidable.
    - apply OracleSemiDecidable_semi_decidable, decidable_empty_set.
  Qed.

  Corollary ce_turing_reducible_zero_jump (A : nat_set) :
    computably_enumerable A -> turing_reducible A zero_jump.
  Proof.
    intro HA. apply red_m_impl_red_T, ce_iff_many_one_zero_jump, HA.
  Qed.

  Theorem zero_jump_computably_enumerable :
    computably_enumerable zero_jump.
  Proof.
    unfold computably_enumerable, zero_jump, turing_jump.
    eapply OracleSemiDecidable_semi_decidable.
    - apply decidable_empty_set.
    - apply semidecidable_J.
  Qed.

  Theorem complement_zero_jump_not_computably_enumerable :
    ~ computably_enumerable (fun n => ~ zero_jump n).
  Proof.
    intros Hco.
    eapply (not_semidecidable_compl_J (Q := empty_set)).
    apply semi_decidable_OracleSemiDecidable.
    exact Hco.
  Qed.

  Corollary zero_jump_undecidable : ~ decidable zero_jump.
  Proof.
    intro Hdec.
    apply complement_zero_jump_not_computably_enumerable.
    unfold computably_enumerable.
    now apply decidable_compl_semi_decidable.
  Qed.

  (** Thus [zero_jump] is a many-one (and hence Turing) complete c.e. set. *)
  Theorem zero_jump_ce_complete :
    computably_enumerable zero_jump /\
    forall A, computably_enumerable A -> A ⪯ₘ zero_jump.
  Proof.
    split.
    - apply zero_jump_computably_enumerable.
    - intros A. now apply ce_iff_many_one_zero_jump.
  Qed.
End CEAndTheJump.
