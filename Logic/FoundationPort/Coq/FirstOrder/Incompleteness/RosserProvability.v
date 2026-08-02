(** Standard-natural semantics of Rosser provability.

    The source also constructs an internal Sigma-one arithmetic formula for
    this predicate and packages it as an abstract provability operator over
    [I Sigma_1].  This module deliberately stops at the external semantics:
    proof witnesses are ordinary natural numbers, and every accepted witness
    decodes to an actual first-order derivation.  Consequently the two
    consistency arguments below are constructive and do not need the
    source's nonstandard-bound or absoluteness machinery.

    The internal Sigma-one formula, its definedness/definability instances,
    the two internal [I Sigma_1] derivability theorems, and the final
    provability-abstraction adapters remain outside this tranche. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  GenericEntailment GenericCalculus
  PropositionalEntailmentInt PropositionalEntailmentClassical.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Calculus2.
From Foundation.FirstOrder.Bootstrapping Require Import Syntax.
From Foundation.FirstOrder.Bootstrapping.DerivabilityCondition Require Import
  D1.
From Foundation.FirstOrder.Incompleteness Require Import WitnessComparison.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Negation commutes with the canonical serialization of closed sentences. *)
Lemma boot_sentence_code_neg : forall L EL (sigma : sentence L),
  boot_sentence_code EL (semiformula_neg sigma) =
  boot_formula_neg_code EL 0 (boot_sentence_code EL sigma).
Proof.
  intros L EL sigma. unfold boot_sentence_code.
  rewrite first_order_sentence_embed_neg.
  apply boot_typed_formula_quote_neg.
Qed.

(** A code is Rosser-provable when it has a proof witness no later than any
    proof witness for its executable syntactic negation. *)
Definition boot_rosser_provable {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (phi : nat) : Prop :=
  @boot_provability_comparison_le L EL T ET phi
    (boot_formula_neg_code EL 0 phi).

Definition boot_sentence_rosser_provable {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (sigma : sentence L) : Prop :=
  @boot_rosser_provable L EL T ET (boot_sentence_code EL sigma).

(** The raw Rosser predicate has the expected interpretation on every typed
    proposition quote.  No claim is made about negation of malformed codes. *)
Lemma boot_rosser_quote : forall L EL T ET (p : proposition L),
  @boot_rosser_provable L EL T ET (boot_typed_formula_quote EL p) <->
  @boot_provability_comparison_le L EL T ET
    (boot_typed_formula_quote EL p)
    (boot_typed_formula_quote EL (boot_typed_formula_neg p)).
Proof.
  intros L EL T ET p. unfold boot_rosser_provable.
  now rewrite boot_typed_formula_quote_neg.
Qed.

Lemma boot_sentence_rosser_quote : forall L EL T ET
    (sigma : sentence L),
  @boot_sentence_rosser_provable L EL T ET sigma <->
  @boot_provability_comparison_le L EL T ET
    (boot_sentence_code EL sigma)
    (boot_sentence_code EL (semiformula_neg sigma)).
Proof.
  intros L EL T ET sigma. unfold boot_sentence_rosser_provable,
    boot_rosser_provable.
  now rewrite boot_sentence_code_neg.
Qed.

(** Explicit proof-witness forms of the preceding quotation laws. *)
Lemma boot_rosser_quote_witness_iff : forall L EL T ET
    (p : proposition L),
  @boot_rosser_provable L EL T ET (boot_typed_formula_quote EL p) <->
  exists b,
    @boot_proof L EL T ET b (boot_typed_formula_quote EL p) /\
    forall b', b' < b ->
      ~ @boot_proof L EL T ET b'
          (boot_typed_formula_quote EL (boot_typed_formula_neg p)).
Proof.
  intros L EL T ET p. rewrite boot_rosser_quote.
  reflexivity.
Qed.

Lemma boot_sentence_rosser_witness_iff : forall L EL T ET
    (sigma : sentence L),
  @boot_sentence_rosser_provable L EL T ET sigma <->
  exists b,
    @boot_proof L EL T ET b (boot_sentence_code EL sigma) /\
    forall b', b' < b ->
      ~ @boot_proof L EL T ET b'
          (boot_sentence_code EL (semiformula_neg sigma)).
Proof.
  intros L EL T ET sigma. rewrite boot_sentence_rosser_quote.
  reflexivity.
Qed.

(** Rosser provability forgets to ordinary raw-code provability. *)
Lemma boot_rosser_provable_to_provable : forall L EL T ET phi,
  @boot_rosser_provable L EL T ET phi ->
  @boot_provable L EL T ET phi.
Proof.
  intros L EL T ET phi H.
  exact (@boot_provability_comparison_le_to_provable
    L EL T ET phi (boot_formula_neg_code EL 0 phi) H).
Qed.

(** An accepted standard proof witness for a sentence decodes to a genuine
    theorem of the ambient first-order theory. *)
Lemma boot_standard_proof_sound : forall L EL T ET code
    (sigma : sentence L),
  @boot_proof L EL T ET code (boot_sentence_code EL sigma) ->
  first_order_theory_provable T sigma.
Proof.
  intros L EL T ET code sigma Hcode.
  apply (@boot_sentence_provable_sound L T EL ET sigma).
  now exists code.
Qed.

Corollary boot_sentence_rosser_provable_sound : forall L EL T ET
    (sigma : sentence L),
  @boot_sentence_rosser_provable L EL T ET sigma ->
  first_order_theory_provable T sigma.
Proof.
  intros L EL T ET sigma Hrosser.
  apply (@boot_sentence_provable_sound L T EL ET sigma).
  apply (@boot_rosser_provable_to_provable L EL T ET
    (boot_sentence_code EL sigma)).
  exact Hrosser.
Qed.

(** Generic first-order consistency rules out simultaneous proofs of a
    sentence and its negation. *)
Lemma first_order_consistent_not_both : forall L (T : theory L)
    (sigma : sentence L),
  generic_consistent (first_order_theory_entailment L) T ->
  first_order_theory_provable T sigma ->
  first_order_theory_provable T (semiformula_neg sigma) -> False.
Proof.
  intros L T sigma Hconsistent Hsigma Hneg.
  apply (generic_consistent_not_inconsistent Hconsistent).
  eapply generic_intuitionistic_inconsistent_of_provable_neg.
  - exact (generic_intuitionistic_of_classical
      (first_order_theory_classical T)).
  - exact Hsigma.
  - exact Hneg.
Qed.

(** A theorem of a consistent theory is Rosser-provable.  Since witnesses
    are standard naturals, consistency excludes every opposing proof code;
    no minimal-witness choice is needed. *)
Theorem boot_rosser_internalize : forall L EL T ET
    (sigma : sentence L),
  generic_consistent (first_order_theory_entailment L) T ->
  first_order_theory_provable T sigma ->
  @boot_rosser_provable L EL T ET (boot_sentence_code EL sigma).
Proof.
  intros L EL T ET sigma Hconsistent Hsigma.
  apply (proj2 (@boot_sentence_rosser_witness_iff
    L EL T ET sigma)).
  destruct (@boot_internalize_provability L T EL ET sigma Hsigma)
    as [code Hcode].
  exists code. split; [exact Hcode |].
  intros opposing _ Hopposing.
  apply (@first_order_consistent_not_both L T sigma Hconsistent Hsigma).
  exact (@boot_standard_proof_sound L EL T ET opposing
    (semiformula_neg sigma) Hopposing).
Qed.

Corollary boot_sentence_rosser_internalize : forall L EL T ET
    (sigma : sentence L),
  generic_consistent (first_order_theory_entailment L) T ->
  first_order_theory_provable T sigma ->
  @boot_sentence_rosser_provable L EL T ET sigma.
Proof.
  intros L EL T ET sigma Hconsistent Hsigma.
  exact (@boot_rosser_internalize L EL T ET sigma Hconsistent Hsigma).
Qed.

(** Conversely, a proof of the negation in a consistent theory excludes
    Rosser provability.  The comparison already contains a proof of the
    positive sentence, so its ordering side condition is irrelevant here. *)
Theorem boot_not_rosser_provable : forall L EL T ET
    (sigma : sentence L),
  generic_consistent (first_order_theory_entailment L) T ->
  first_order_theory_provable T (semiformula_neg sigma) ->
  ~ @boot_rosser_provable L EL T ET (boot_sentence_code EL sigma).
Proof.
  intros L EL T ET sigma Hconsistent Hneg Hrosser.
  apply (@first_order_consistent_not_both L T sigma Hconsistent).
  - apply (@boot_sentence_provable_sound L T EL ET sigma).
    apply (@boot_rosser_provable_to_provable L EL T ET
      (boot_sentence_code EL sigma)).
    exact Hrosser.
  - exact Hneg.
Qed.

Corollary boot_not_sentence_rosser_provable : forall L EL T ET
    (sigma : sentence L),
  generic_consistent (first_order_theory_entailment L) T ->
  first_order_theory_provable T (semiformula_neg sigma) ->
  ~ @boot_sentence_rosser_provable L EL T ET sigma.
Proof.
  intros L EL T ET sigma Hconsistent Hneg.
  exact (@boot_not_rosser_provable L EL T ET sigma Hconsistent Hneg).
Qed.
