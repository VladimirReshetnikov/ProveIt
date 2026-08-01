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
  RawCodedDynamicTruthImpBranchExclusivity
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
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
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

(** Generic one-step represented implication transport.  The source and
    target are arbitrary ordinary PA formulas; the only formula-specific
    input is an ordinary PA proof of their implication.  The theorem keeps
    an arbitrary adequate template prefix fixed while allowing the standard
    PA witness tail to grow. *)
Theorem raw_codedPALocalProofOf_target_of_PA_implication_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext prefix
      sourceFormula targetFormula sourceRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  Formula.BProv Formula.Ax_s nil (pImp sourceFormula targetFormula) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawQuotedFormulaCode M sourceFormula) sourceRoot ->
  exists targetWitnessList targetContext targetRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawQuotedFormulaCode M targetFormula) targetRoot.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    prefix sourceFormula targetFormula sourceRoot hprefix hsource
    himplication hsourceRoot.
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation hagreement sourceWitnessList sourceContext
      (pImp sourceFormula targetFormula) hsource himplication)
    as (witnesses & implicationRoot & htargetWitnessed &
      himplicationRoot).
  set (targetWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses sourceWitnessList).
  set (targetContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses sourceContext).
  assert (hincluded : RawContextListIncluded M
      sourceContext targetContext).
  {
    unfold targetContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA witnesses sourceContext).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      targetWitnessList targetContext prefix
      (rawQuotedFormulaCode M sourceFormula) sourceRoot
      hsource htargetWitnessed hincluded hsourceRoot)
    as [transportedSourceRoot htransportedSource].
  pose proof
    (raw_codedPAAxiomWitnessContext_context_realizable M
      targetWitnessList targetContext htargetWitnessed)
    as htargetRealizable.
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    targetContext prefix
    (rawTemplateFormula translation
      (embedPAFormula (pImp sourceFormula targetFormula)))
    implicationRoot htargetRealizable hprefix himplicationRoot)
    as [prefixedImplicationRoot hprefixedImplication].
  rewrite (rawTemplateFormula_embedPA hagreement
    (pImp sourceFormula targetFormula)) in hprefixedImplication.
  rewrite rawQuotedFormulaCode_imp in hprefixedImplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawQuotedFormulaCode M sourceFormula)
    (rawQuotedFormulaCode M targetFormula)
    prefixedImplicationRoot transportedSourceRoot
    hprefixedImplication htransportedSource) as htargetRoot.
  lazymatch type of htargetRoot with
  | RawCodedPALocalProofOf _ _ _ ?targetRoot =>
      exists targetWitnessList, targetContext, targetRoot;
      split; [exact htargetWitnessed |];
      split; [exact hincluded | exact htargetRoot]
  end.
Qed.

(** Dependency-ordered paired form.  The second implication is compiled on
    the extension selected by the first; the first result and the second
    source are transported explicitly so the conclusion shares one final
    witnessed tail. *)
Theorem raw_codedPALocalProofOf_pair_of_PA_implications_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext prefix
      sigmaSourceFormula sigmaTargetFormula
      piSourceFormula piTargetFormula sigmaSourceRoot piSourceRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  Formula.BProv Formula.Ax_s nil
    (pImp sigmaSourceFormula sigmaTargetFormula) ->
  Formula.BProv Formula.Ax_s nil
    (pImp piSourceFormula piTargetFormula) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawQuotedFormulaCode M sigmaSourceFormula) sigmaSourceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawQuotedFormulaCode M piSourceFormula) piSourceRoot ->
  exists targetWitnessList targetContext sigmaTargetRoot piTargetRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawQuotedFormulaCode M sigmaTargetFormula) sigmaTargetRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawQuotedFormulaCode M piTargetFormula) piTargetRoot.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    prefix sigmaSourceFormula sigmaTargetFormula
    piSourceFormula piTargetFormula sigmaSourceRoot piSourceRoot
    hprefix hsource hsigmaImplication hpiImplication
    hsigmaSource hpiSource.
  destruct
    (raw_codedPALocalProofOf_target_of_PA_implication_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext prefix
      sigmaSourceFormula sigmaTargetFormula sigmaSourceRoot
      hprefix hsource hsigmaImplication hsigmaSource)
    as (sigmaWitnessList & sigmaContext & sigmaTargetRoot &
      hsigmaWitnessed & hsourceSigmaIncluded & hsigmaTarget).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sourceWitnessList sourceContext
      sigmaWitnessList sigmaContext prefix
      (rawQuotedFormulaCode M piSourceFormula) piSourceRoot
      hsource hsigmaWitnessed hsourceSigmaIncluded hpiSource)
    as [transportedPiSourceRoot htransportedPiSource].
  destruct
    (raw_codedPALocalProofOf_target_of_PA_implication_under_prefix
      M hPA translation hagreement sigmaWitnessList sigmaContext prefix
      piSourceFormula piTargetFormula transportedPiSourceRoot
      hprefix hsigmaWitnessed hpiImplication htransportedPiSource)
    as (targetWitnessList & targetContext & piTargetRoot &
      htargetWitnessed & hsigmaTargetIncluded & hpiTarget).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation sigmaWitnessList sigmaContext
      targetWitnessList targetContext prefix
      (rawQuotedFormulaCode M sigmaTargetFormula) sigmaTargetRoot
      hsigmaWitnessed htargetWitnessed hsigmaTargetIncluded hsigmaTarget)
    as [transportedSigmaTargetRoot htransportedSigmaTarget].
  assert (hsourceTargetIncluded : RawContextListIncluded M
      sourceContext targetContext).
  {
    intros member hmember.
    exact (hsigmaTargetIncluded member
      (hsourceSigmaIncluded member hmember)).
  }
  exists targetWitnessList, targetContext,
    transportedSigmaTargetRoot, piTargetRoot.
  split; [exact htargetWitnessed |].
  split; [exact hsourceTargetIncluded |].
  split; assumption.
Qed.

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
  exact
    (raw_codedPALocalProofOf_pair_of_PA_implications_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext prefix
      dynamicTruthZeroInputGlobalSigmaApplicationFormula
      dynamicTruthZeroSigmaEvidenceFormula
      dynamicTruthZeroInputGlobalPiApplicationFormula
      dynamicTruthZeroPiEvidenceFormula
      sigmaApplicationRoot piApplicationRoot hprefix hsource
      PA_proves_dynamicTruthZeroInputGlobalSigmaApplicationNativeForwardFormula
      PA_proves_dynamicTruthZeroInputGlobalPiApplicationNativeForwardFormula
      hsigmaApplication hpiApplication).
Qed.

(** Converse transport.  Native evidence and canonical applications are now
    interchangeable proof resources under every adequate temporary prefix,
    not merely semantically equivalent formulas. *)
Theorem
    raw_dynamicTruthZeroCanonicalApplicationRoots_of_nativeEvidenceRoots_under_prefix :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext prefix sigmaEvidenceRoot
      piEvidenceRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
    sigmaEvidenceRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula)
    piEvidenceRoot ->
  exists targetWitnessList targetContext sigmaApplicationRoot
      piApplicationRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      sigmaApplicationRoot /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      piApplicationRoot.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    prefix sigmaEvidenceRoot piEvidenceRoot hprefix hsource hsigma hpi.
  exact
    (raw_codedPALocalProofOf_pair_of_PA_implications_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext prefix
      dynamicTruthZeroSigmaEvidenceFormula
      dynamicTruthZeroInputGlobalSigmaApplicationFormula
      dynamicTruthZeroPiEvidenceFormula
      dynamicTruthZeroInputGlobalPiApplicationFormula
      sigmaEvidenceRoot piEvidenceRoot hprefix hsource
      PA_proves_dynamicTruthZeroInputGlobalSigmaApplicationNativeBackwardFormula
      PA_proves_dynamicTruthZeroInputGlobalPiApplicationNativeBackwardFormula
      hsigma hpi).
Qed.

(** Two PA implications map a binary disjunction without selecting either
    branch metatheoretically.  This ordinary-PA lemma is deliberately
    formula-generic; soundness supplies the two semantic branch maps, and
    open completeness packages their disjunction as one PA derivation. *)
Theorem PA_proves_disjunction_map_of_implications : forall
    leftSource rightSource leftTarget rightTarget,
  Formula.BProv Formula.Ax_s nil (pImp leftSource leftTarget) ->
  Formula.BProv Formula.Ax_s nil (pImp rightSource rightTarget) ->
  Formula.BProv Formula.Ax_s nil
    (pImp (pOr leftSource rightSource)
      (pOr leftTarget rightTarget)).
Proof.
  intros leftSource rightSource leftTarget rightTarget
    hleftImp hrightImp.
  apply PA_proves_open_formula_of_raw_valid.
  intros M hPA e.
  cbn [raw_formula_sat].
  intros [hleft | hright].
  - left.
    pose proof
      (raw_sat_of_BProv_axs M (pImp leftSource leftTarget)
        hPA hleftImp e) as himp.
    cbn [raw_formula_sat] in himp.
    exact (himp hleft).
  - right.
    pose proof
      (raw_sat_of_BProv_axs M (pImp rightSource rightTarget)
        hPA hrightImp e) as himp.
    cbn [raw_formula_sat] in himp.
    exact (himp hright).
Qed.

(** Represented counterpart of [PA_proves_disjunction_map_of_implications].
    The source disjunction is transported by one compiled PA theorem, so the
    result requires one witness extension rather than independently growing
    and subsequently merging two branch contexts. *)
Theorem
    raw_codedPALocalProofOf_disjunction_targets_of_PA_implications_under_prefix
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext prefix
      leftSource rightSource leftTarget rightTarget decisionRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  Formula.BProv Formula.Ax_s nil (pImp leftSource leftTarget) ->
  Formula.BProv Formula.Ax_s nil (pImp rightSource rightTarget) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawFormulaOrCode M
      (rawQuotedFormulaCode M leftSource)
      (rawQuotedFormulaCode M rightSource)) decisionRoot ->
  exists targetWitnessList targetContext targetDecisionRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawFormulaOrCode M
        (rawQuotedFormulaCode M leftTarget)
        (rawQuotedFormulaCode M rightTarget)) targetDecisionRoot.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    prefix leftSource rightSource leftTarget rightTarget decisionRoot
    hprefix hsource hleftImp hrightImp hdecision.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawQuotedFormulaCode M (pOr leftSource rightSource))
    decisionRoot) in hdecision.
  destruct
    (raw_codedPALocalProofOf_target_of_PA_implication_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext prefix
      (pOr leftSource rightSource) (pOr leftTarget rightTarget)
      decisionRoot hprefix hsource
      (PA_proves_disjunction_map_of_implications
        leftSource rightSource leftTarget rightTarget
        hleftImp hrightImp)
      hdecision)
    as (targetWitnessList & targetContext & targetDecisionRoot &
      htargetWitnessed & hincluded & htargetDecision).
  exists targetWitnessList, targetContext, targetDecisionRoot.
  split; [exact htargetWitnessed |].
  split; [exact hincluded |].
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation targetContext prefix)
    (rawFormulaOrCode M
      (rawQuotedFormulaCode M leftTarget)
      (rawQuotedFormulaCode M rightTarget)) targetDecisionRoot)
    in htargetDecision.
  exact htargetDecision.
Qed.

(** Preserve a rank-zero decision while changing its two payloads from the
    native fixed certificates to the canonical global applications.  A
    single PA implication is compiled, so the two alternatives remain in
    one represented disjunction and choose only one common witness
    extension.  This is strictly weaker than the paired transport above. *)
Theorem
    raw_dynamicTruthZeroCanonicalApplicationDecision_of_nativeEvidenceDecision_under_prefix
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext prefix decisionRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation prefix ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext prefix)
    (rawFormulaOrCode M
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula))
    decisionRoot ->
  exists targetWitnessList targetContext applicationDecisionRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation targetContext prefix)
      (rawFormulaOrCode M
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalSigmaApplicationFormula)
        (rawQuotedFormulaCode M
          dynamicTruthZeroInputGlobalPiApplicationFormula))
      applicationDecisionRoot.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    prefix decisionRoot hprefix hsource hdecision.
  exact
    (raw_codedPALocalProofOf_disjunction_targets_of_PA_implications_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext prefix
      dynamicTruthZeroSigmaEvidenceFormula
      dynamicTruthZeroPiEvidenceFormula
      dynamicTruthZeroInputGlobalSigmaApplicationFormula
      dynamicTruthZeroInputGlobalPiApplicationFormula decisionRoot
      hprefix hsource
      PA_proves_dynamicTruthZeroInputGlobalSigmaApplicationNativeBackwardFormula
      PA_proves_dynamicTruthZeroInputGlobalPiApplicationNativeBackwardFormula
      hdecision).
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

(** Closed-prefix converse specialization. *)
Corollary
    raw_dynamicTruthZeroCanonicalApplicationRoots_of_nativeEvidenceRoots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall sourceWitnessList sourceContext sigmaEvidenceRoot piEvidenceRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M sourceContext
    (rawQuotedFormulaCode M dynamicTruthZeroSigmaEvidenceFormula)
    sigmaEvidenceRoot ->
  RawCodedPALocalProofOf M sourceContext
    (rawQuotedFormulaCode M dynamicTruthZeroPiEvidenceFormula)
    piEvidenceRoot ->
  exists targetWitnessList targetContext sigmaApplicationRoot
      piApplicationRoot,
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext /\
    RawContextListIncluded M sourceContext targetContext /\
    RawCodedPALocalProofOf M targetContext
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalSigmaApplicationFormula)
      sigmaApplicationRoot /\
    RawCodedPALocalProofOf M targetContext
      (rawQuotedFormulaCode M
        dynamicTruthZeroInputGlobalPiApplicationFormula)
      piApplicationRoot.
Proof.
  intros M hPA translation hagreement sourceWitnessList sourceContext
    sigmaEvidenceRoot piEvidenceRoot hsource hsigma hpi.
  pose proof
    (raw_dynamicTruthZeroCanonicalApplicationRoots_of_nativeEvidenceRoots_under_prefix
      M hPA translation hagreement sourceWitnessList sourceContext nil
      sigmaEvidenceRoot piEvidenceRoot
      (fun formula hformula => match hformula with end)
      hsource hsigma hpi) as hresult.
  cbn [rawTemplateContextCodeOnTail] in hresult.
  exact hresult.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeZeroCanonicalApplicationProofTransport.
