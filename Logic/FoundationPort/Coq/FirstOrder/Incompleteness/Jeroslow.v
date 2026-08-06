(** Standard-natural semantics of refutability.

    Foundation internally represents refutability by a Sigma-one arithmetic
    formula saying that the executable syntactic negation has a proof.  At
    the standard natural numbers, the checked proof serializer gives a
    simpler exact account: refutability of a sentence is theoremhood of its
    negation.  This module records that account both at raw codes and at
    typed closed sentences.

    The representation-independent Jeroslow fixed-point argument and the
    unprovability of the formalized law of noncontradiction are already
    checked by [ProvabilityAbstraction] as [pa_unprovable_jeroslow] and
    [pa_unprovable_flon].  What remains outside this tranche is the internal
    Sigma-one refutability formula, its definedness/definability instances,
    and its concrete arithmetic fixed-point, soundness, and formalized-
    completeness adapters.  Those require internal Delta-one proof
    recognition, arithmetic negation graphs, and object-theory reasoning;
    none is assumed here. *)

From FoundationModal Require Import GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Calculus2.
From Foundation.FirstOrder.Bootstrapping Require Import Syntax.
From Foundation.FirstOrder.Bootstrapping.DerivabilityCondition Require Import
  D1.
From Foundation.FirstOrder.Incompleteness Require Import
  ProvabilityAbstraction RosserProvability.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** A raw formula code is refutable when its executable syntactic negation
    has an accepted standard proof code. *)
Definition boot_refutable {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (phi : nat) : Prop :=
  @boot_provable L EL T ET (boot_formula_neg_code EL 0 phi).

Definition boot_sentence_refutable {L}
    (EL : language_encodable L) (T : theory L)
    (ET : boot_theory_encoding EL T) (sigma : sentence L) : Prop :=
  @boot_refutable L EL T ET (boot_sentence_code EL sigma).

(** On a typed proposition quote, raw syntactic negation is exactly typed
    formula negation. *)
Lemma boot_refutable_quote : forall L EL T ET (p : proposition L),
  @boot_refutable L EL T ET (boot_typed_formula_quote EL p) <->
  @boot_provable L EL T ET
    (boot_typed_formula_quote EL (boot_typed_formula_neg p)).
Proof.
  intros L EL T ET p. unfold boot_refutable.
  now rewrite boot_typed_formula_quote_neg.
Qed.

(** The closed-sentence form reuses the quotation law factored by the
    Rosser layer. *)
Lemma boot_sentence_refutable_quote : forall L EL T ET
    (sigma : sentence L),
  @boot_sentence_refutable L EL T ET sigma <->
  @boot_provable L EL T ET
    (boot_sentence_code EL (semiformula_neg sigma)).
Proof.
  intros L EL T ET sigma. unfold boot_sentence_refutable,
    boot_refutable.
  now rewrite boot_sentence_code_neg.
Qed.

(** Refutability exposes an ordinary proof witness for the syntactic
    negation code. *)
Lemma boot_sentence_refutable_witness_iff : forall L EL T ET
    (sigma : sentence L),
  @boot_sentence_refutable L EL T ET sigma <->
  exists code,
    @boot_proof L EL T ET code
      (boot_formula_neg_code EL 0 (boot_sentence_code EL sigma)).
Proof. reflexivity. Qed.

(** Exact standard-model semantics: a sentence is refutable precisely when
    its typed negation is a theorem of the original theory. *)
Theorem boot_sentence_refutable_iff_theory : forall L T EL ET
    (sigma : sentence L),
  @boot_sentence_refutable L EL T ET sigma <->
  first_order_theory_provable T (semiformula_neg sigma).
Proof.
  intros L T EL ET sigma.
  rewrite boot_sentence_refutable_quote.
  change (@boot_sentence_provable L EL T ET
    (semiformula_neg sigma) <->
    first_order_theory_provable T (semiformula_neg sigma)).
  apply boot_sentence_provable_iff_theory.
Qed.

(** External theoremhood of a negation serializes to a raw refutation code. *)
Theorem boot_internalize_refutation : forall L T EL ET
    (sigma : sentence L),
  first_order_theory_provable T (semiformula_neg sigma) ->
  exists code,
    @boot_proof L EL T ET code
      (boot_formula_neg_code EL 0 (boot_sentence_code EL sigma)).
Proof.
  intros L T EL ET sigma Hneg.
  destruct (@boot_internalize_provability L T EL ET
    (semiformula_neg sigma) Hneg) as [code Hcode].
  exists code. now rewrite <- boot_sentence_code_neg.
Qed.

Corollary boot_internalize_refutability : forall L T EL ET
    (sigma : sentence L),
  first_order_theory_provable T (semiformula_neg sigma) ->
  @boot_sentence_refutable L EL T ET sigma.
Proof.
  intros L T EL ET sigma Hneg.
  apply (proj2 (@boot_sentence_refutable_witness_iff
    L EL T ET sigma)).
  exact (@boot_internalize_refutation L T EL ET sigma Hneg).
Qed.

(** Conversely, every accepted raw refutation witness decodes to a genuine
    derivation of the typed negated sentence. *)
Theorem boot_standard_refutation_sound : forall L T EL ET code
    (sigma : sentence L),
  @boot_proof L EL T ET code
      (boot_formula_neg_code EL 0 (boot_sentence_code EL sigma)) ->
  first_order_theory_provable T (semiformula_neg sigma).
Proof.
  intros L T EL ET code sigma Hcode.
  apply (@boot_standard_proof_sound L EL T ET code
    (semiformula_neg sigma)).
  now rewrite boot_sentence_code_neg.
Qed.

Corollary boot_sentence_refutable_sound : forall L T EL ET
    (sigma : sentence L),
  @boot_sentence_refutable L EL T ET sigma ->
  first_order_theory_provable T (semiformula_neg sigma).
Proof.
  intros L T EL ET sigma Hrefutable.
  apply (proj1 (@boot_sentence_refutable_iff_theory
    L T EL ET sigma)).
  exact Hrefutable.
Qed.

(** Generic first-order consistency makes ordinary sentence provability and
    refutability incompatible.  The proof reuses the Rosser layer's factored
    consistency lemma after exact readback of both standard proof codes. *)
Theorem boot_sentence_consistent_not_both : forall L T EL ET
    (sigma : sentence L),
  generic_consistent (first_order_theory_entailment L) T ->
  ~ (@boot_sentence_provable L EL T ET sigma /\
     @boot_sentence_refutable L EL T ET sigma).
Proof.
  intros L T EL ET sigma Hconsistent [Hprovable Hrefutable].
  eapply (@first_order_consistent_not_both L T sigma Hconsistent).
  - exact (@boot_sentence_provable_sound L T EL ET sigma Hprovable).
  - exact (@boot_sentence_refutable_sound L T EL ET sigma Hrefutable).
Qed.

Corollary boot_sentence_provable_not_refutable : forall L T EL ET
    (sigma : sentence L),
  generic_consistent (first_order_theory_entailment L) T ->
  @boot_sentence_provable L EL T ET sigma ->
  ~ @boot_sentence_refutable L EL T ET sigma.
Proof.
  intros L T EL ET sigma Hconsistent Hprovable Hrefutable.
  apply (@boot_sentence_consistent_not_both L T EL ET sigma Hconsistent).
  now split.
Qed.

Corollary boot_sentence_refutable_not_provable : forall L T EL ET
    (sigma : sentence L),
  generic_consistent (first_order_theory_entailment L) T ->
  @boot_sentence_refutable L EL T ET sigma ->
  ~ @boot_sentence_provable L EL T ET sigma.
Proof.
  intros L T EL ET sigma Hconsistent Hrefutable Hprovable.
  apply (@boot_sentence_consistent_not_both L T EL ET sigma Hconsistent).
  now split.
Qed.
