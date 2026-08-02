(**
  Standard-natural Hilbert--Bernays D1 for executable proof codes.

  This ports the computational content of
  [Bootstrapping/DerivabilityCondition/D1.lean].  The source works inside an
  arbitrary nonstandard arithmetic model.  At the standard natural numbers,
  the checked proof serializer and its converse soundness theorem give the
  stronger exact equivalence between external theoremhood and raw-code
  provability.
*)

From Stdlib Require Import Lists.List.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Coding Calculus Calculus2.
From Foundation.FirstOrder.Bootstrapping Require Import Syntax.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The raw code used for a closed sentence agrees with both the typed and
    empty-free-variable quotation interfaces. *)
Definition boot_sentence_code {L}
    (EL : language_encodable L) (sigma : sentence L) : nat :=
  boot_typed_formula_quote EL (first_order_sentence_embed sigma).

Lemma boot_sentence_code_closed_quote : forall L EL (sigma : sentence L),
  boot_sentence_code EL sigma = boot_closed_formula_quote EL sigma.
Proof.
  intros. unfold boot_sentence_code, first_order_sentence_embed.
  apply boot_closed_formula_quote_emb.
Qed.

Definition boot_sentence_provable {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (sigma : sentence L) : Prop :=
  @boot_provable L EL T ET (boot_sentence_code EL sigma).

(** Quoting a proof-relevant finite-context derivation produces an accepted
    raw derivation code with exactly the pointwise quoted consequence. *)
Theorem boot_derivable_quote : forall L T EL ET Gamma,
  first_order_derivable2 T Gamma ->
  exists code,
    @boot_derivation_of L EL T ET code
      (map (boot_typed_formula_quote EL) Gamma).
Proof.
  intros L T EL ET Gamma [d].
  exists (@boot_derivation2_quote L T Gamma EL ET d).
  apply boot_derivation2_quote_recognized.
Qed.

(** Hilbert--Bernays D1: external theoremhood can be serialized into internal
    standard-natural proof-code provability. *)
Theorem boot_internalize_provability : forall L T EL ET
    (sigma : sentence L),
  first_order_theory_provable T sigma ->
  @boot_sentence_provable L EL T ET sigma.
Proof.
  intros L T EL ET sigma H.
  unfold boot_sentence_provable, boot_sentence_code.
  apply (proj2 (@boot_provable_quote_iff L EL T ET
    (first_order_sentence_embed sigma))).
  apply (proj1 (@first_order_theory_provable_iff_derivable2 L T sigma)).
  exact H.
Qed.

(** At the standard model there is no gap in either direction: accepted raw
    proof codes reconstruct typed derivations, and typed derivations serialize
    back to accepted codes.  This strictly strengthens source D1. *)
Theorem boot_sentence_provable_iff_theory : forall L T EL ET
    (sigma : sentence L),
  @boot_sentence_provable L EL T ET sigma <->
  first_order_theory_provable T sigma.
Proof.
  intros L T EL ET sigma.
  unfold boot_sentence_provable, boot_sentence_code.
  rewrite boot_provable_quote_iff.
  symmetry. apply first_order_theory_provable_iff_derivable2.
Qed.

Corollary boot_sentence_provable_sound : forall L T EL ET
    (sigma : sentence L),
  @boot_sentence_provable L EL T ET sigma ->
  first_order_theory_provable T sigma.
Proof.
  intros L T EL ET sigma H.
  exact (proj1 (@boot_sentence_provable_iff_theory L T EL ET sigma) H).
Qed.
