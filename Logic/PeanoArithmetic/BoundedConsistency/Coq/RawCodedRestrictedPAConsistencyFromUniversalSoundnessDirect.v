(**
  Direct-code consistency from universal derivation soundness.

  The original consistency bridge is phrased over finite structural template
  inputs.  Its proof-tree construction is valid, but that interface cannot
  carry a genuinely nonstandard truth formula because an opaque carrier code
  need not decode to a finite metatheoretic formula tree.  Derivation
  soundness is therefore now compiled through direct structural inputs, whose
  opaque leaves carry represented shift and opening relations themselves.

  This module closes the representation mismatch at the next seam.  It gives
  the context-truth, bottom-refutation, restricted-consistency target, and
  fixed implication their exact direct codes.  It then verifies the same
  implication-introduction construction as the finite bridge.  The only open
  premise is the honest body compiler which must actually instantiate the
  universal soundness invariant and use the two truth-coherence laws.

  No direct input is converted to a finite structural input, no carrier
  formula is decoded, and no semantic assertion is promoted to a PA proof.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedProofImpIConstructor
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

Module PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierStrongPrefixDirectInductionShell.

(** ------------------------------------------------------------------
    Exact direct-code views. *)

Definition rawCoqRestrictedPAAxiomContextsTruthDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPAAxiomContextsTruthTemplate.

Definition rawCoqRestrictedPABottomTruthRefutationDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPABottomTruthRefutationTemplate.

Definition rawCoqRestrictedPAConsistencyFromSoundnessTargetDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPAConsistencyFromUniversalSoundnessTargetTemplate.

Definition rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPAConsistencyFromUniversalSoundnessBridgeTemplate.

Arguments rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPAConsistencyFromSoundnessTargetDirectCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectCode M inputs
  : clear implicits.

(** The target contains no opaque leaves.  Consequently the symbol-level
    restricted-target theorem applies directly to the symbols carried by a
    direct translation, independently of its nonstandard operation traces. *)
Theorem raw_coqRestrictedPAConsistencyFromSoundnessTargetDirectCode_exact :
    forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqRestrictedPAConsistencyFromSoundnessTargetDirectCode M inputs =
  rawRestrictedTargetFormulaContextCode M
    (rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm)
    restrictedPAConsistencyFormulaContext.
Proof.
  intros M inputs.
  unfold rawCoqRestrictedPAConsistencyFromSoundnessTargetDirectCode,
    coqRestrictedPAConsistencyFromUniversalSoundnessTargetTemplate,
    rawDirectTemplateFormula, rawDirectTemplateTerm.
  apply rawStructuralWith_restrictedPAConsistencyTemplate.
Qed.

(** This view is deliberately proved through small constructor equations.
    Asking Rocq to normalize both concrete children of the bridge at once is
    needlessly expensive and obscures the exact direct endpoints. *)
Theorem raw_coqRestrictedPAConsistencyFromSoundnessBridgeDirectCode_view :
    forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectCode M inputs =
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    (rawRestrictedTargetFormulaContextCode M
      (rawDirectTemplateTerm inputs
        coqRestrictedPASoundnessLowerLevelTerm)
      restrictedPAConsistencyFormulaContext).
Proof.
  intros M inputs.
  unfold rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectCode,
    coqRestrictedPAConsistencyFromUniversalSoundnessBridgeTemplate.
  rewrite rawDirectTemplateFormula_imp_code.
  rewrite <- raw_coqRestrictedPADerivationSoundnessUniversalDirectCode_view.
  unfold coqRestrictedPAConsistencyFromUniversalSoundnessTargetTemplate,
    rawDirectTemplateFormula, rawDirectTemplateTerm.
  rewrite rawStructuralWith_restrictedPAConsistencyTemplate.
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Direct selected-truth support. *)

Definition rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (numeralCode baseContext : M) : M :=
  rawListNode M
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext).

Arguments rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
  M inputs numeralCode baseContext : clear implicits.

(** The selected truth formula and both coherence laws must live in the
    literal context used by the consistency bridge.  The package is purely
    syntactic: each component is an ordinary checked local PA derivation. *)
Definition RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot : M) : Prop :=
  RawCodedPAAxiomWitnessContext M witnessList baseContext /\
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    nextAxiomSoundness nextAxiomSoundnessRoot /\
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawFormulaImpCode M nextAxiomSoundness
      (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs))
    coherenceRoot /\
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPABottomTruthRefutationDirectCode M inputs)
    bottomRefutationRoot.

Arguments RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport
  M inputs numeralCode witnessList baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot
  : clear implicits.

Definition rawCoqRestrictedPAAxiomContextsTruthDirectRoot
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (numeralCode baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot : M) : M :=
  rawProofImpERoot M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    nextAxiomSoundness
    (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs)
    coherenceRoot nextAxiomSoundnessRoot.

Arguments rawCoqRestrictedPAAxiomContextsTruthDirectRoot
  M inputs numeralCode baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot : clear implicits.

Theorem raw_coqRestrictedPAAxiomContextsTruthDirect_of_selected_support :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot,
  RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport M inputs
    numeralCode witnessList baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot ->
  RawCodedPALocalProofOf M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs)
    (rawCoqRestrictedPAAxiomContextsTruthDirectRoot M inputs
      numeralCode baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot).
Proof.
  intros M hPA inputs numeralCode witnessList baseContext
    nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
    bottomRefutationRoot (_ & hnextAxiom & hcoherence & _).
  unfold rawCoqRestrictedPAAxiomContextsTruthDirectRoot.
  exact (raw_codedPALocalProofOf_impE M hPA
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    nextAxiomSoundness
    (rawCoqRestrictedPAAxiomContextsTruthDirectCode M inputs)
    coherenceRoot nextAxiomSoundnessRoot hcoherence hnextAxiom).
Qed.

(** ------------------------------------------------------------------
    The exact open body seam and verified implication introduction. *)

Definition RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectOpenCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot,
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
    RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport M inputs
      numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot ->
    exists child : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeBodyDirectContextCode
          M inputs numeralCode baseContext)
        (rawRestrictedTargetFormulaContextCode M numeralCode
          restrictedPAConsistencyFormulaContext)
        child.

Arguments
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectOpenCompiler
  M inputs : clear implicits.

Definition rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectRoot
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (numeralCode baseContext child : M) : M :=
  rawProofImpIRoot M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    (rawRestrictedTargetFormulaContextCode M numeralCode
      restrictedPAConsistencyFormulaContext)
    child.

Arguments rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectRoot
  M inputs numeralCode baseContext child : clear implicits.

Theorem raw_coqRestrictedPAConsistencyFromSoundnessBridgeDirect_of_open :
    forall (M : RawPAModel), RawPASatisfies M ->
  forall (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPAConsistencyFromUniversalSoundnessDirectOpenCompiler
    M inputs ->
  forall numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot,
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = numeralCode ->
    RawCoqRestrictedPASelectedAxiomContextTruthDirectSupport M inputs
      numeralCode witnessList baseContext nextAxiomSoundness
      nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot ->
    exists bridgeRoot : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPAConsistencyBridgeContextCode
          M numeralCode baseContext)
        (rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectCode M inputs)
        bridgeRoot.
Proof.
  intros M hPA inputs hopen numeralCode witnessList baseContext
    nextAxiomSoundness nextAxiomSoundnessRoot coherenceRoot
    bottomRefutationRoot hlevel hsupport.
  destruct (hopen numeralCode witnessList baseContext nextAxiomSoundness
    nextAxiomSoundnessRoot coherenceRoot bottomRefutationRoot
    hlevel hsupport) as [child hchild].
  exists (rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectRoot M
    inputs numeralCode baseContext child).
  unfold rawCoqRestrictedPAConsistencyFromSoundnessBridgeDirectRoot.
  rewrite raw_coqRestrictedPAConsistencyFromSoundnessBridgeDirectCode_view,
    hlevel.
  exact (raw_codedPALocalProofOf_impI M hPA
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M numeralCode baseContext)
    (rawCoqRestrictedPADerivationSoundnessUniversalDirectCode M inputs)
    (rawRestrictedTargetFormulaContextCode M numeralCode
      restrictedPAConsistencyFormulaContext)
    child hchild).
Qed.

End PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirect.
