(**
  Identify the Or-I-left truth residual with its native Sigma application.

  The public rule dispatcher phrases the law through an opaque five-argument
  conclusion-truth leaf.  Native truth selection realizes that leaf by a
  dependent ternary application of the selected successor Sigma predicate.
  This file rewrites both occurrences of the leaf at carrier-code level and
  isolates the honest native target:

      code(outer = left \/ right) -> Sigma(left) -> Sigma(outer).

  No closure property of an arbitrary predicate is assumed.  The linked
  compiler interface at the end explicitly requires the same global
  successor edge and application selector carried by the native package.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedSyntaxConstructors
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateNumeralParameters
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTernaryApplication
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth
  RawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeLawTransport.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAssumption.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterOrIntroductionLeftTruth.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessNativeDirectClosureRemainder.

(** The literal native target.  Formula and assignment arguments are passed
    through the same direct term view used by the opaque-leaf equation, so no
    independent application or substitution witness can enter here. *)
Definition rawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawCode
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode) : M :=
  rawFormulaImpCode M
    (rawDirectTemplateFormula inputs
      coqRestrictedPADirectOrIntroductionLeftFormulaCodeTemplate)
    (rawFormulaImpCode M
      (rawTernaryApplicationOutput sigmaSelector
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters coqRestrictedPADirectAssumptionWitnessFormulaTerm)
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters (ttVar 9))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters (ttVar 8)))
      (rawTernaryApplicationOutput sigmaSelector
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters (embedPATerm (liftTerm 8 (tVar 2))))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters (ttVar 9))
        (rawCoqRestrictedPADerivationSoundnessTemplateTermView
          M parameters (ttVar 8)))).

Arguments rawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawCode
  M parameters inputs sigmaCode sigmaSelector : clear implicits.

(** Both public truth leaves are applications of the same dependent Sigma
    selector.  The two displayed hierarchy parameters disappear only through
    the audited conclusion-leaf equation, never by treating them as arbitrary
    or definitionally irrelevant. *)
Theorem raw_coqRestrictedPADirectOrIntroductionLeftNativeTruthLaw_code :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  rawDirectTemplateFormula inputs
    coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate =
  rawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawCode
    M parameters inputs sigmaCode sigmaSelector.
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector hconclusion.
  change (rawTemplateFormula
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate =
    rawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawCode
      M parameters inputs sigmaCode sigmaSelector).
  rewrite rawTemplateFormula_orIntroductionLeftDynamicTruthLaw_view.
  unfold rawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawCode.
  f_equal.
  f_equal.
  - unfold coqRestrictedPADirectOrIntroductionLeftFormulaTruthTemplate,
      coqRestrictedPADirectAssumptionWitnessFormulaTruthTemplate.
    exact (hconclusion
      coqRestrictedPASoundnessLowerLevelTerm
      coqRestrictedPASoundnessUpperLevelTerm
      coqRestrictedPADirectAssumptionWitnessFormulaTerm
      (ttVar 9) (ttVar 8)).
  - rewrite coqRestrictedPADirectOrIntroductionLeft_result_truth_shape.
    exact (hconclusion
      coqRestrictedPASoundnessLowerLevelTerm
      coqRestrictedPASoundnessUpperLevelTerm
      (embedPATerm (liftTerm 8 (tVar 2)))
      (ttVar 9) (ttVar 8)).
Qed.

Definition RawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail))
      (rawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawCode
        M parameters inputs sigmaCode sigmaSelector)
      root.

Arguments RawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawRoot
  M hPA parameters inputs sigmaCode sigmaSelector tail : clear implicits.

(** Code equality transports any proof-producing native construction into the
    exact public residual expected by the dispatcher. *)
Theorem raw_publicOrIntroductionLeftTruthLawRoot_of_native : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  forall tail,
  RawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawRoot
    M hPA parameters inputs sigmaCode sigmaSelector tail ->
  RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
    M hPA inputs tail.
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector hconclusion tail [root hroot].
  exists root.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail))
    (rawDirectTemplateFormula inputs
      coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate)
    root).
  pose proof
    (raw_coqRestrictedPADirectOrIntroductionLeftNativeTruthLaw_code
      M hPA parameters contextTruth conclusionTruth sigmaCode sigmaSelector
      hconclusion) as hlaw.
  change (rawDirectTemplateFormula inputs
      coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate =
    rawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawCode
      M parameters inputs sigmaCode sigmaSelector) in hlaw.
  rewrite hlaw.
  exact hroot.
Qed.

(** The dynamic reroot source already has exactly the same ready-context
    shell as the native law.  The only apparent mismatch is the conclusion
    truth leaf: after the native selector has been chosen, the audited leaf
    equation identifies that leaf with the corresponding Sigma application.
    Consequently the native law is obtained by a literal code rewrite; no
    new proof-producing successor callback is needed at this point. *)
Theorem raw_nativeOrIntroductionLeftTruthLawRoot_of_dynamic_reroot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  forall tail,
  RawCoqRestrictedPADirectOrIntroductionLeftDynamicTruthLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawRoot
    M hPA parameters inputs sigmaCode sigmaSelector tail.
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector hconclusion tail [root hroot].
  exists root.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqRestrictedPADirectStrongStepOrIntroductionLeftReadyContext tail))
    (rawDirectTemplateFormula inputs
      coqRestrictedPADirectOrIntroductionLeftDynamicTruthLawTemplate)
    root).
  pose proof
    (raw_coqRestrictedPADirectOrIntroductionLeftNativeTruthLaw_code
      M hPA parameters contextTruth conclusionTruth sigmaCode sigmaSelector
      hconclusion) as hlaw.
  rewrite <- hlaw.
  exact hroot.
Qed.

Definition RawCoqRestrictedPADirectSelectedNativeOrIntroductionLeftTruthTail
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode) : Prop :=
  exists witnesses : StandardPAAxiomWitnessPrefix,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (embedPAContext (map witnessedAxiom witnesses))) /\
    RawCoqRestrictedPADirectOrIntroductionLeftNativeTruthLawRoot
      M hPA parameters inputs sigmaCode sigmaSelector
      (embedPAContext (map witnessedAxiom witnesses)).

Arguments
  RawCoqRestrictedPADirectSelectedNativeOrIntroductionLeftTruthTail
  M hPA parameters inputs sigmaCode sigmaSelector : clear implicits.

Theorem raw_selectedPublicOrIntroductionLeftTruthTail_of_native : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  RawCoqRestrictedPADirectSelectedNativeOrIntroductionLeftTruthTail
    M hPA parameters inputs sigmaCode sigmaSelector ->
  RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail
    M hPA inputs.
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector hconclusion
    (witnesses & hwitnessed & hnative).
  exists witnesses. split; [exact hwitnessed |].
  exact
    (raw_publicOrIntroductionLeftTruthLawRoot_of_native
      M hPA parameters contextTruth conclusionTruth sigmaCode sigmaSelector
      hconclusion (embedPAContext (map witnessedAxiom witnesses)) hnative).
Qed.

(** The preceding rewrite can be applied at the selected witnessed tail
    produced by the unconditional dynamic reroot compiler.  This is the
    useful interface for the native direct-truth package: its conclusion
    leaf equation supplies [hconclusion], while the dynamic source supplies
    the actual local proof root. *)
Theorem raw_selectedNativeOrIntroductionLeftTruthTail_of_dynamic_reroot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (contextTruth conclusionTruth :
      RawCoqRestrictedPATruthDirectSelector M parameters),
  let inputs :=
    rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
      M hPA parameters contextTruth conclusionTruth in
  forall sigmaCode
    (sigmaSelector : RawCodedTernaryApplicationSelector M sigmaCode),
  (forall first second third fourth fifth,
    rawDirectTemplateFormula inputs
      (tfOpaque coqRestrictedPAConclusionTruthPredicateName
        [first; second; third; fourth; fifth]) =
    rawTernaryApplicationOutput sigmaSelector
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters third)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fourth)
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters fifth)) ->
  RawCoqRestrictedPADirectSelectedNativeOrIntroductionLeftTruthTail
    M hPA parameters inputs sigmaCode sigmaSelector.
Proof.
  intros M hPA parameters contextTruth conclusionTruth inputs
    sigmaCode sigmaSelector hconclusion.
  destruct
    (raw_dynamicRestrictedRerootLawRoot_on_selected_witnessed_tail
      M hPA inputs) as
    (witnesses & hdynamicWitnessed & hdynamicRoot).
  exists witnesses. split; [exact hdynamicWitnessed |].
  apply
    (raw_nativeOrIntroductionLeftTruthLawRoot_of_dynamic_reroot
      M hPA parameters contextTruth conclusionTruth sigmaCode sigmaSelector
      hconclusion
      (embedPAContext (map witnessedAxiom witnesses))).
  exact hdynamicRoot.
Qed.

(** Smallest linked proof-producing boundary.  Unlike a universal callback
    over arbitrary predicates, this compiler receives the actual paired
    successor edge that constructed [nextGlobalSigma] and the dependent
    selector for that same code. *)
Definition
    RawCoqRestrictedPADirectLinkedNativeOrIntroductionLeftTruthCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall currentGlobalSigma currentGlobalPi predecessorLevel
      nextGlobalSigma nextGlobalPi
      (sigmaSelector :
        RawCodedTernaryApplicationSelector M nextGlobalSigma),
    RawDynamicTruthPairedGlobalSuccessorAt M
      currentGlobalSigma currentGlobalPi (raw_succ M predecessorLevel)
      nextGlobalSigma nextGlobalPi ->
    RawCoqRestrictedPADirectSelectedNativeOrIntroductionLeftTruthTail
      M hPA parameters inputs nextGlobalSigma sigmaSelector.

Arguments
  RawCoqRestrictedPADirectLinkedNativeOrIntroductionLeftTruthCompiler
  M hPA parameters inputs : clear implicits.

(** Extract the exact selected public field from the coherent native package.
    The linked compiler is instantiated only after the package has exposed its
    dependent truth selectors and the successor edge that generated them. *)
Theorem
    raw_selectedPublicOrIntroductionLeftTruthTail_of_nativeDirectTruthInputsWithClosureAt
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  (forall contextTruth conclusionTruth,
    RawCoqRestrictedPADirectLinkedNativeOrIntroductionLeftTruthCompiler
      M hPA parameters
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)) ->
  exists contextTruth conclusionTruth,
    RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth).
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs hcompiler.
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hinputs.
  destruct hinputs as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     closureCount & axiom & hsuccessor & hsigmaDeep & hcontextDeep &
     hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
     hconclusionLeaf & hselectorNative & hconclusionNative & happlication &
     hremainder).
  subst inputs.
  exists contextTruth, conclusionTruth.
  apply
    (raw_selectedPublicOrIntroductionLeftTruthTail_of_native
      M hPA parameters contextTruth conclusionTruth
      nextGlobalSigma sigmaApplicationSelector hconclusionLeaf).
  exact
    (hcompiler contextTruth conclusionTruth
      currentGlobalSigma currentGlobalPi predecessorLevel
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector hsuccessor).
Qed.

(** Native direct-truth inputs now need no separate linked Or-I-left
    compiler.  The selected conclusion leaf equation and the dynamic reroot
    source suffice to build the native tail directly; the successor edge is
    still retained by the input package for the other native fields. *)
Theorem
    raw_selectedPublicOrIntroductionLeftTruthTail_of_nativeDirectTruthInputsWithClosureAt_of_dynamic_reroot
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  exists contextTruth conclusionTruth,
    RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth).
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs.
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hinputs.
  destruct hinputs as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     closureCount & axiom & hsuccessor & hsigmaDeep & hcontextDeep &
     hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
     hconclusionLeaf & hselectorNative & hconclusionNative & happlication &
     hremainder).
  subst inputs.
  exists contextTruth, conclusionTruth.
  apply
    (raw_selectedPublicOrIntroductionLeftTruthTail_of_native
      M hPA parameters contextTruth conclusionTruth nextGlobalSigma
      sigmaApplicationSelector hconclusionLeaf).
  exact
    (raw_selectedNativeOrIntroductionLeftTruthTail_of_dynamic_reroot
      M hPA parameters contextTruth conclusionTruth nextGlobalSigma
      sigmaApplicationSelector hconclusionLeaf).
Qed.

(** End-to-end endpoint after the dynamic reroot transport.  Compared with
    the linked endpoint below, this version exposes no Or-I-left successor
    callback: the native package's conclusion leaf is rewritten directly to
    the dynamic reroot root, and only the post-Or continuation remains. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_nativeDirectTruthInputsWithClosureAt_of_dynamic_reroot
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  (forall contextTruth conclusionTruth,
    RawCoqRestrictedPADirectRemainingAfterOrIntroductionLeftTruthStandardTailCompiler
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)) ->
  exists contextTruth conclusionTruth soundnessCertificate,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      soundnessCertificate.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs hremaining.
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hinputs.
  destruct hinputs as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     closureCount & axiom & hsuccessor & hsigmaDeep & hcontextDeep &
     hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
     hconclusionLeaf & hselectorNative & hconclusionNative & happlication &
     hremainder).
  subst inputs.
  assert (hselected :
    RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)).
  {
    apply
      (raw_selectedPublicOrIntroductionLeftTruthTail_of_native
        M hPA parameters contextTruth conclusionTruth
        nextGlobalSigma sigmaApplicationSelector hconclusionLeaf).
    exact
      (raw_selectedNativeOrIntroductionLeftTruthTail_of_dynamic_reroot
        M hPA parameters contextTruth conclusionTruth nextGlobalSigma
        sigmaApplicationSelector hconclusionLeaf).
  }
  pose proof
    (raw_remainingAfterAssumptionCompiler_of_selectedOrIntroductionLeftTruth
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      hselected (hremaining contextTruth conclusionTruth))
    as hremainingAfterAssumption.
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_remaining_afterAssumption
      M hPA parameters contextTruth conclusionTruth
      nextGlobalSigma sigmaApplicationSelector contextApplicationSelector
      hconclusionLeaf hcontextLeaf hremainingAfterAssumption
      hconclusionLeaf hcontextLeaf hremainingAfterAssumption
      (rawCoqRestrictedPADirectClosureReplacement M)
      axiom closureCount hremainder)
    as [soundnessCertificate hsoundness].
  exists contextTruth, conclusionTruth, soundnessCertificate.
  exact hsoundness.
Qed.

(** End-to-end native package endpoint for this field.  Once the linked
    compiler constructs the native Or law, only the exact twenty-field
    continuation remains; Assumption, Or-I-left recursion, closure selection,
    and all dependent selector equations are discharged by existing verified
    compilers. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_linkedNativeOrIntroductionLeftTruth
    : forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
      (parameters : RawCodedTemplateNumeralParameters M)
      currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence,
  RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt M hPA parameters
    currentGlobalSigma currentGlobalPi predecessorLevel nextSigmaEvidence ->
  (forall contextTruth conclusionTruth,
    RawCoqRestrictedPADirectLinkedNativeOrIntroductionLeftTruthCompiler
      M hPA parameters
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)) ->
  (forall contextTruth conclusionTruth,
    RawCoqRestrictedPADirectRemainingAfterOrIntroductionLeftTruthStandardTailCompiler
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)) ->
  exists contextTruth conclusionTruth soundnessCertificate,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M
        (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
          M hPA parameters contextTruth conclusionTruth))
      soundnessCertificate.
Proof.
  intros M hPA parameters currentGlobalSigma currentGlobalPi
    predecessorLevel nextSigmaEvidence hinputs hcompiler hremaining.
  unfold RawCoqRestrictedPANativeDirectTruthInputsWithClosureAt in hinputs.
  destruct hinputs as
    (nextGlobalSigma & nextGlobalPi & sigmaApplicationSelector &
     contextApplicationSelector & contextTruth & conclusionTruth & inputs &
     closureCount & axiom & hsuccessor & hsigmaDeep & hcontextDeep &
     hinputs & hcontextOutput & hconclusionOutput & hcontextLeaf &
     hconclusionLeaf & hselectorNative & hconclusionNative & happlication &
     hremainder).
  subst inputs.
  assert (hselected :
    RawCoqRestrictedPADirectSelectedOrIntroductionLeftTruthTail M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)).
  {
    apply
      (raw_selectedPublicOrIntroductionLeftTruthTail_of_native
        M hPA parameters contextTruth conclusionTruth
        nextGlobalSigma sigmaApplicationSelector hconclusionLeaf).
    exact
      (hcompiler contextTruth conclusionTruth
        currentGlobalSigma currentGlobalPi predecessorLevel
        nextGlobalSigma nextGlobalPi sigmaApplicationSelector hsuccessor).
  }
  pose proof
    (raw_remainingAfterAssumptionCompiler_of_selectedOrIntroductionLeftTruth
      M hPA
      (rawCoqRestrictedPADerivationSoundnessTemplateDirectStructuralInputs
        M hPA parameters contextTruth conclusionTruth)
      hselected (hremaining contextTruth conclusionTruth))
    as hremainingAfterAssumption.
  destruct
    (raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversalDirect_of_remaining_afterAssumption
      M hPA parameters contextTruth conclusionTruth
      nextGlobalSigma sigmaApplicationSelector contextApplicationSelector
      hconclusionLeaf hcontextLeaf hremainingAfterAssumption
      (rawCoqRestrictedPADirectClosureReplacement M)
      axiom closureCount hremainder)
    as [soundnessCertificate hsoundness].
  exists contextTruth, conclusionTruth, soundnessCertificate.
  exact hsoundness.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessOrIntroductionLeftNativeLawTransport.
