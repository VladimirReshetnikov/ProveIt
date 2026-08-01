(**
  Represented proof transport for the canonical rank-zero global applications.

  The semantic equivalence module proves two ordinary PA implications from
  the canonical first-successor applications to the fixed native level-one
  evidence formulas.  This module materializes both implications over one
  witnessed PA tail, transports caller-supplied application roots through the
  chosen witness prefixes, and performs the two represented modus-ponens
  steps under an arbitrary adequate temporary template prefix.

  Keeping this composition independent of the predecessor callback is useful:
  any proof-producing global traversal may return the two canonical
  application roots and reuse the same transport.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

Module
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationProofTransport.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalTraceExactification.

(** Quotation is compositional at implication nodes.  Naming this conversion
    keeps later proof endpoints folded instead of reducing both large
    application and certificate syntax trees. *)
Lemma rawQuotedFormulaCode_imp : forall (M : RawPAModel) left right,
  rawQuotedFormulaCode M (pImp left right) =
  rawFormulaImpCode M
    (rawQuotedFormulaCode M left) (rawQuotedFormulaCode M right).
Proof. reflexivity. Qed.

(** Transport a pair of canonical application roots to the native evidence
    roots on one common witnessed extension.  The temporary prefix is kept
    completely abstract; only its ordinary atomic-adequacy invariant is
    needed for inserting the two fixed PA implications. *)
Theorem
    raw_dynamicTruthZeroNativeEvidenceRoots_of_canonicalApplicationRoots_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext prefix sigmaApplicationRoot
      piApplicationRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    sigmaApplicationRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula)
    piApplicationRoot ->
  exists targetWitnessList targetContext sigmaEvidenceRoot piEvidenceRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
      sigmaEvidenceRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula)
      piEvidenceRoot.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    prefix sigmaApplicationRoot piApplicationRoot hprefix hsource
    hsigmaApplication hpiApplication.

  (** Materialize the Sigma implication first. *)
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation hagreement sourceWitnessList sourceContext
      dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula
      hsource
      PA_proves_dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula)
    as (sigmaWitnesses & sigmaImplicationRoot & hsigmaWitnessed &
      hsigmaImplication).
  set (sigmaWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      sigmaWitnesses sourceWitnessList).
  set (sigmaContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      sigmaWitnesses sourceContext).
  assert (hsourceSigmaIncluded :
      RawContextListIncluded M sourceContext sigmaContext).
  {
    unfold sigmaContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA sigmaWitnesses sourceContext).
  }

  (** Materialize the Pi implication above the first selected extension. *)
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation hagreement sigmaWitnessList sigmaContext
      dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula
      hsigmaWitnessed
      PA_proves_dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula)
    as (piWitnesses & piImplicationRoot & htargetWitnessed &
      hpiImplication).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      piWitnesses sigmaWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      piWitnesses sigmaContext).
  assert (hsigmaTargetIncluded :
      RawContextListIncluded M sigmaContext targetContext).
  {
    unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA piWitnesses sigmaContext).
  }
  assert (hsourceTargetIncluded :
      RawContextListIncluded M sourceContext targetContext).
  {
    intros member hmember.
    exact (hsigmaTargetIncluded member
      (hsourceSigmaIncluded member hmember)).
  }

  (** Move the first implication and both caller roots to the final tail. *)
  assert (hsigmaImplicationEmpty : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sigmaContext nil)
      (rawTemplateFormula translation
        (embedPAFormula
          dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula))
      sigmaImplicationRoot).
  { cbn [rawTemplateContextCodeOnTail]. exact hsigmaImplication. }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sigmaWitnessList sigmaContext
      targetWitnessList targetContext nil
      (rawTemplateFormula translation
        (embedPAFormula
          dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula))
      sigmaImplicationRoot hsigmaWitnessed htargetWitnessed
      hsigmaTargetIncluded hsigmaImplicationEmpty)
    as [transportedSigmaImplicationRoot htransportedSigmaImplication].
  cbn [rawTemplateContextCodeOnTail] in htransportedSigmaImplication.

  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      sigmaApplicationRoot hsource htargetWitnessed hsourceTargetIncluded
      hsigmaApplication)
    as [transportedSigmaApplicationRoot htransportedSigmaApplication].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      piApplicationRoot hsource htargetWitnessed hsourceTargetIncluded
      hpiApplication)
    as [transportedPiApplicationRoot htransportedPiApplication].

  (** Insert the same temporary prefix above both fixed implications. *)
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      targetWitnessList targetContext htargetWitnessed)
    as htargetRealizable.
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    targetContext prefix
    (rawTemplateFormula translation
      (embedPAFormula
        dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula))
    transportedSigmaImplicationRoot htargetRealizable hprefix
    htransportedSigmaImplication)
    as [prefixedSigmaImplicationRoot hprefixedSigmaImplication].
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    targetContext prefix
    (rawTemplateFormula translation
      (embedPAFormula
        dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula))
    piImplicationRoot htargetRealizable hprefix hpiImplication)
    as [prefixedPiImplicationRoot hprefixedPiImplication].

  (** Agreement converts embedded ordinary PA syntax to structural
      quotation; implication compositionality then exposes the exact two
      [Imp-E] endpoints without reducing either large formula. *)
  rewrite (rawTemplateFormula_embedPA hagreement
    dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula)
    in hprefixedSigmaImplication.
  unfold dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula
    in hprefixedSigmaImplication.
  rewrite rawQuotedFormulaCode_imp in hprefixedSigmaImplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
    prefixedSigmaImplicationRoot transportedSigmaApplicationRoot
    hprefixedSigmaImplication htransportedSigmaApplication)
    as hsigmaEvidence.

  rewrite (rawTemplateFormula_embedPA hagreement
    dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula)
    in hprefixedPiImplication.
  unfold dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula
    in hprefixedPiImplication.
  rewrite rawQuotedFormulaCode_imp in hprefixedPiImplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula)
    (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula)
    prefixedPiImplicationRoot transportedPiApplicationRoot
    hprefixedPiImplication htransportedPiApplication)
    as hpiEvidence.

  lazymatch type of hsigmaEvidence with
  | RawCodedPALocalProofOf _ _ _ ?sigmaEvidenceRoot =>
      lazymatch type of hpiEvidence with
      | RawCodedPALocalProofOf _ _ _ ?piEvidenceRoot =>
          exists targetWitnessList, targetContext,
            sigmaEvidenceRoot, piEvidenceRoot;
          split; [exact htargetWitnessed |];
          split; [exact hsourceTargetIncluded |];
          split; [exact hsigmaEvidence | exact hpiEvidence]
      end
  end.
Qed.

(** Empty-prefix specialization for clients whose application roots already
    live directly on a witnessed PA context. *)
Corollary
    raw_dynamicTruthZeroNativeEvidenceRoots_of_canonicalApplicationRoots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext sigmaApplicationRoot
      piApplicationRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M sourceContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalSigmaApplicationFormula)
    sigmaApplicationRoot ->
  RawCodedPALocalProofOf M sourceContext
    (rawQuotedFormulaCode M
      dynamicTruthZeroInputGlobalPiApplicationFormula)
    piApplicationRoot ->
  exists targetWitnessList targetContext sigmaEvidenceRoot piEvidenceRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M targetContext
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
      sigmaEvidenceRoot /\
    RawCodedPALocalProofOf M targetContext
      (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula)
      piEvidenceRoot.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    sigmaApplicationRoot piApplicationRoot hsource hsigma hpi.
  pose proof
    (raw_dynamicTruthZeroNativeEvidenceRoots_of_canonicalApplicationRoots_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext nil
      sigmaApplicationRoot piApplicationRoot
      (fun formula hformula => match hformula with end)
      hsource hsigma hpi) as hresult.
  cbn [rawTemplateContextCodeOnTail] in hresult.
  exact hresult.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationProofTransport.
