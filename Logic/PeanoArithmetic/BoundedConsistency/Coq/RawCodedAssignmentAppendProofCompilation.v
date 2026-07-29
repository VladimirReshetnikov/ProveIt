(**
  Proof-code compilation of the PA-internal beta-table append theorem.

  [RawCodedFixedLevelTruthTotality] already proves in ordinary PA that any
  represented assignment table defined below [bound] can be extended by one
  arbitrary carrier value.  The global truth traversal needs that theorem
  inside a model-coded local proof, specialized to four terms which may live
  under nonstandard traversal witnesses.

  This module uses the generic universal-elimination chain compiler to open
  all four binders.  It returns the resulting proof on a standard witnessed
  PA-axiom prefix, ready to be merged with the child traversal proof.  No
  semantic completeness step is performed here beyond the already audited
  fixed theorem [PA_proves_codedAssignmentAppendFormula].
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAListCoding Require Import ListCode.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedFixedLevelTruthTotality
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedPALocalProofUniversalEliminationChain.

Import ListNotations.

Module PABoundedRawCodedAssignmentAppendProofCompilation.

Import PA.
Import PAListCode.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.

(** The exact four openings, in the same outer-to-inner order as
    [RawCodedAssignmentAppendLaw]: old table code, old table step, old bound,
    and the value appended at that bound. *)
Definition coqCodedAssignmentAppendInstanceTemplate
    (oldCode oldStep bound newValue : TemplateTerm) : TemplateFormula :=
  match templateUniversalOpenMany
    (embedPAFormula codedAssignmentAppendFormula)
    [oldCode; oldStep; bound; newValue] with
  | Some target => target
  | None => tfBot
  end.

(** The fallback branch is unreachable: the fixed source has literally four
    leading universal quantifiers.  Keeping this reduction theorem named
    avoids repeating a large [cbn] calculation in every proof client. *)
Lemma coqCodedAssignmentAppendInstanceTemplate_open_many : forall
    oldCode oldStep bound newValue,
  templateUniversalOpenMany
    (embedPAFormula codedAssignmentAppendFormula)
    [oldCode; oldStep; bound; newValue] =
  Some (coqCodedAssignmentAppendInstanceTemplate
    oldCode oldStep bound newValue).
Proof.
  intros oldCode oldStep bound newValue.
  unfold coqCodedAssignmentAppendInstanceTemplate,
    codedAssignmentAppendFormula, fixedTruthTotalityAll4.
  reflexivity.
Qed.

(** Specialize the fixed theorem on an arbitrary witnessed base.  The direct
    structural inputs affect only how the four replacement terms are coded;
    the embedded arithmetic theorem itself contains no opaque leaves. *)
Theorem raw_codedPALocalProofOf_assignment_append_instance_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext oldCode oldStep bound newValue,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawDirectTemplateFormula inputs
        (coqCodedAssignmentAppendInstanceTemplate
          oldCode oldStep bound newValue)) root.
Proof.
  intros M hPA inputs baseWitnessList baseContext
    oldCode oldStep bound newValue hbase.
  exact
    (raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail
      M hPA
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      baseWitnessList baseContext codedAssignmentAppendFormula
      [oldCode; oldStep; bound; newValue]
      (coqCodedAssignmentAppendInstanceTemplate
        oldCode oldStep bound newValue)
      hbase PA_proves_codedAssignmentAppendFormula
      (coqCodedAssignmentAppendInstanceTemplate_open_many
        oldCode oldStep bound newValue)).
Qed.

(** Empty-base form used by independently selected soundness fields.  Its
    finite witness batch may later be surrounded by the generic standard-tail
    transport without changing the specialized append conclusion. *)
Corollary raw_codedPALocalProofOf_assignment_append_instance_standard_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    oldCode oldStep bound newValue,
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (rawDirectTemplateFormula inputs
        (coqCodedAssignmentAppendInstanceTemplate
          oldCode oldStep bound newValue)) root.
Proof.
  intros M hPA inputs oldCode oldStep bound newValue.
  apply (raw_codedPALocalProofOf_assignment_append_instance_on_witnessed_tail
    M hPA inputs (raw_zero M) (raw_zero M)
    oldCode oldStep bound newValue).
  pose proof (raw_codedPAAxiomWitnessContext_standard M hPA []) as hempty.
  cbn [rawQuotedPAAxiomWitnessList rawListCode map] in hempty.
  exact hempty.
Qed.

End PABoundedRawCodedAssignmentAppendProofCompilation.
