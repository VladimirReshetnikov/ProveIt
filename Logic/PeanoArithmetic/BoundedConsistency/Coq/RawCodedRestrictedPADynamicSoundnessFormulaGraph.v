(**
  Output-first graph for the nonstandard dynamic-soundness formula code.

  The fixed source formula has one distinguished free variable for the proof
  restriction level.  At a carrier-valued level this graph first chooses a
  represented numeral-term code and then performs represented single
  substitution into that source.  Thus the graph remains meaningful at
  nonstandard model elements and never decodes a level in Rocq.

  The previously verified explicit substitution tree supplies an exact
  witness whose output is [rawRestrictedPADynamicSoundnessImplicationCode].
  This module only packages that construction as the output-first graph
  convention consumed by the six-field master assembler.
*)

From Stdlib Require Import Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedRestrictedPADynamicSoundnessComposition
  RawCodedRestrictedPADynamicSoundnessSource
  RawCodedRestrictedPADynamicSoundnessSubstitution.

Module PABoundedRawCodedRestrictedPADynamicSoundnessFormulaGraph.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedRestrictedPADynamicSoundnessComposition.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSource.
Import PABoundedRawCodedRestrictedPADynamicSoundnessSubstitution.

(** Outside the existential binder the environment is

      output :: level :: tail.

    Inside it is [numeralCode :: output :: level :: tail]. *)
Definition restrictedPADynamicSoundnessFormulaCodeGraph : formula :=
  pEx
    (pAnd
      (numeralTermCodeAtTermAt (tVar 2) (tVar 0))
      (codedFormulaSingleSubstitutionTermAt
        (tVar 0)
        (Term.numeral
          (formulaCode restrictedPADynamicSoundnessSourceFormula))
        (tVar 1))).

Definition RawRestrictedPADynamicSoundnessFormulaCodeAt
    (M : RawPAModel) (level output : M) : Prop :=
  exists numeralCode : M,
    RawNumeralTermCodeAt M level numeralCode /\
    RawCodedFormulaSingleSubstitution M numeralCode
      (rawRestrictedPADynamicSoundnessSourceCode M) output.

Arguments RawRestrictedPADynamicSoundnessFormulaCodeAt
  M level output : clear implicits.

(** Exact arbitrary-model semantics.  PA identifies the closed source
    quotation with its internal numeral code. *)
Theorem restrictedPADynamicSoundnessFormulaCodeGraph_representation : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    restrictedPADynamicSoundnessFormulaCodeGraph <->
  RawRestrictedPADynamicSoundnessFormulaCodeAt M level output.
Proof.
  intros M hPA tail level output.
  unfold restrictedPADynamicSoundnessFormulaCodeGraph,
    RawRestrictedPADynamicSoundnessFormulaCodeAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_numeralTermCodeAtTermAt_iff.
  setoid_rewrite raw_sat_codedFormulaSingleSubstitutionTermAt_iff.
  cbn [raw_term_eval scons].
  setoid_rewrite raw_term_eval_numeral.
  setoid_rewrite <- (rawQuotedFormulaCode_standard M hPA
    restrictedPADynamicSoundnessSourceFormula).
  reflexivity.
Qed.

(** The explicit substitution tree makes the graph total at every carrier
    level, with the transparent dynamic implication as a chosen output. *)
Theorem raw_restrictedPADynamicSoundnessFormulaCodeGraph_exact : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail level,
  exists numeralCode : M,
    RawNumeralTermCodeAt M level numeralCode /\
    raw_formula_sat M
      (scons M
        (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode)
        (scons M level tail))
      restrictedPADynamicSoundnessFormulaCodeGraph.
Proof.
  intros M hPA tail level.
  destruct (raw_numeralTermCodeExists_all M hPA level)
    as [numeralCode hnumeral].
  exists numeralCode. split; [exact hnumeral |].
  apply (proj2
    (restrictedPADynamicSoundnessFormulaCodeGraph_representation
      M hPA tail level
      (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode))).
  exists numeralCode. split; [exact hnumeral |].
  exact (raw_codedRestrictedPADynamicSoundnessSource_substitution
    M hPA level numeralCode hnumeral).
Qed.

Corollary restrictedPADynamicSoundnessFormulaCodeGraph_raw_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail level,
  exists output : M,
    raw_formula_sat M (scons M output (scons M level tail))
      restrictedPADynamicSoundnessFormulaCodeGraph.
Proof.
  intros M hPA tail level.
  destruct (raw_restrictedPADynamicSoundnessFormulaCodeGraph_exact
    M hPA tail level) as [numeralCode [_ hgraph]].
  exists (rawRestrictedPADynamicSoundnessImplicationCode M numeralCode).
  exact hgraph.
Qed.

End PABoundedRawCodedRestrictedPADynamicSoundnessFormulaGraph.
