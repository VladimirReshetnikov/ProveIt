From Coq Require Import Morphisms.

From SyntheticComputability Require Import EPF partial reductions.
From SyntheticComputability.PostsTheorem Require Import TuringJump.
From SyntheticComputability.TuringReducibility Require Import OracleComputability.
From TuringDegrees Require Import Core.

Section TuringJumpDegrees.
  Context {Part : partiality}.
  Context {unit_encoding : encoding unit}.
  Context {EPF_assm : EPF.EPF}.

  Definition turing_jump (A : nat_set) : nat_set := J A.

  Lemma turing_jump_monotone (A B : nat_set) :
    turing_reducible A B ->
    turing_reducible (turing_jump A) (turing_jump B).
  Proof.
    intro HAB. apply red_m_impl_red_T.
    now apply red_T_imp_red_m_jumps.
  Qed.

  Global Instance turing_jump_Proper :
    Proper (turing_equiv ==> turing_equiv) turing_jump.
  Proof.
    intros A B [HAB HBA]. split; now apply turing_jump_monotone.
  Qed.

  Lemma turing_jump_above (A : nat_set) :
    turing_reducible A (turing_jump A).
  Proof.
    apply red_m_impl_red_T.
    eapply red_m_transitive.
    - exact (proj1 (jump_gt A)).
    - apply red_𝒥_J_self.
  Qed.

  Lemma turing_jump_not_below (A : nat_set) :
    ~ turing_reducible (turing_jump A) A.
  Proof.
    exact (not_turing_red_J (Q := A)).
  Qed.

  (** The jump is strictly increasing at every degree. *)
  Theorem turing_jump_strict (A : nat_set) :
    turing_strict A (turing_jump A).
  Proof.
    split.
    - apply turing_jump_above.
    - apply turing_jump_not_below.
  Qed.

  Definition zero_jump : nat_set := turing_jump empty_set.

  Corollary zero_jump_nonzero : turing_strict empty_set zero_jump.
  Proof.
    apply turing_jump_strict.
  Qed.

  Lemma jump_respects_degree_equality (A B : nat_set) :
    turing_equiv A B -> turing_equiv (turing_jump A) (turing_jump B).
  Proof.
    apply turing_jump_Proper.
  Qed.

  Fixpoint iterated_jump (A : nat_set) (n : nat) : nat_set :=
    match n with
    | 0 => A
    | S k => turing_jump (iterated_jump A k)
    end.

  Lemma iterated_jump_monotone (A B : nat_set) n :
    turing_reducible A B ->
    turing_reducible (iterated_jump A n) (iterated_jump B n).
  Proof.
    intro HAB. induction n as [|n IH]; cbn; auto using turing_jump_monotone.
  Qed.

  Lemma iterated_jump_step_strict (A : nat_set) n :
    turing_strict (iterated_jump A n) (iterated_jump A (S n)).
  Proof.
    cbn. apply turing_jump_strict.
  Qed.
End TuringJumpDegrees.
