(**
  The four structural conjuncts of the projected-field refutation compiler
  are exactly the unfolding of an ordinary PA proof certificate.

  [RawRestrictedPAProjectedFieldRefutationCompiler] asks for five things.
  Its first four outputs — the certificate list view, the witnessed-axiom
  context, rule coverage of the lower proof, and the lower endpoint — are
  literally the four components of [RawCodedPAProofOf] applied to the
  incoming certificate.  They therefore carry no mathematical content and are
  discharged here once and for all.

  What is left after that discharge is named [RawRestrictedPADynamicSoundnessProducer].
  It is the single genuinely proof-producing obligation of the whole
  development: a model-internal coded PA derivation of the six-premise
  dynamic-soundness implication at a possibly nonstandard numeral code, in
  the canonical shifted proof context over an arbitrary witnessed-axiom base.

  Nothing in this file establishes that producer.  The file exists so that
  the remaining premise is stated once, sharply, and in the smallest form
  that still implies the requested PA theorem.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedNumeralTermCode
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedRestrictedPAConsistencyFormulaCode
  CompactPAUniformProvability
  RawCodedRestrictedPADynamicSoundnessComposition
  RawCodedRestrictedPAProjectedFieldRefutation.

Import ListNotations.

Module PABoundedRawCodedRestrictedPADynamicSoundnessProducer.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedCompactPAUniformProvability.
Import PABoundedRawCodedRestrictedPADynamicSoundnessComposition.
Import PABoundedRawCodedRestrictedPAProjectedFieldRefutation.

(** The exact remaining proof-producing obligation.

    Read it as: in an arbitrary PA model, for an arbitrary carrier element
    [value] and an arbitrary numeral-term code [numeralCode] naming it, and
    over an arbitrary witnessed PA-axiom base, PA itself has a proof — coded
    inside the model — of restricted dynamic soundness at level [value].

    No standardness hypothesis is imposed on [value], and this is the whole
    difficulty: at a standard [value] the statement is the internalisation of
    an already established metatheoretic PA theorem, while at a nonstandard
    [value] the derivation must be produced by a model-internal recursion. *)
Definition RawRestrictedPADynamicSoundnessProducer
    (M : RawPAModel) : Prop :=
  forall (value numeralCode baseWitnessList baseContext : M),
    RawNumeralTermCodeAt M value numeralCode ->
    RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
    RawRestrictedPADynamicSoundnessImplicationProof M numeralCode
      (rawRestrictedPACanonicalShiftedProofContextCode
        M baseContext numeralCode).

Arguments RawRestrictedPADynamicSoundnessProducer M : clear implicits.

Definition RawRestrictedPADynamicSoundnessProducerInAllModels : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPADynamicSoundnessProducer M.

(** The structural discharge.  Every conjunct except the last is read off the
    incoming certificate; the last is exactly the producer instance at the
    successor level. *)
Theorem
    raw_restrictedPAProjectedFieldRefutationCompiler_of_dynamicSoundnessProducer
    : forall (M : RawPAModel),
  RawRestrictedPADynamicSoundnessProducer M ->
  RawRestrictedPAProjectedFieldRefutationCompiler M.
Proof.
  intros M hproducer level target certificate successorNumeralCode
    htarget hcertificate hnumeral.
  destruct hcertificate as
    (witnessList & lowerProof & baseContext &
      hview & hwitness & hcoverage & hendpoint).
  exists witnessList, lowerProof, baseContext.
  split; [exact hview |].
  split; [exact hwitness |].
  split; [exact hcoverage |].
  split; [exact hendpoint |].
  exact (hproducer (raw_succ M level) successorNumeralCode
    witnessList baseContext hnumeral hwitness).
Qed.

Corollary
    raw_restrictedPAProjectedFieldRefutationCompilerInAllModels_of_dynamicSoundnessProducer
    : RawRestrictedPADynamicSoundnessProducerInAllModels ->
  RawRestrictedPAProjectedFieldRefutationCompilerInAllModels.
Proof.
  intros hproducer M hPA.
  exact
    (raw_restrictedPAProjectedFieldRefutationCompiler_of_dynamicSoundnessProducer
      M (hproducer M hPA)).
Qed.

(** The requested PA theorem, now carrying exactly one premise: the
    model-internal dynamic-soundness proof producer. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_dynamicSoundnessProducer
    : RawRestrictedPADynamicSoundnessProducerInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hproducer.
  apply
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_projectedFields.
  exact
    (raw_restrictedPAProjectedFieldRefutationCompilerInAllModels_of_dynamicSoundnessProducer
      hproducer).
Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessProducer.
