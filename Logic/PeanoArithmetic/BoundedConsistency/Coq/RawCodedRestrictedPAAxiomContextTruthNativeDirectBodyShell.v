(**
  Open the logical shell around native PA axiom-context truth.

  The selected context-truth statement has two leading universal binders
  followed by three hypotheses: a witnessed PA-axiom context, its bounded
  formula codes, and atomic adequacy of all of its members.  The genuinely
  arithmetic part of the proof is a synchronized traversal of the witness
  list and the context list.  This module separates that traversal from all
  proof-tree plumbing.

  More precisely, the residual compiler below is asked only for the final
  selected context application in the context obtained after both binder
  shifts and all three assumptions.  Universal and implication introduction
  then build the complete body root.  All contexts in this reduction are
  literal raw codes; no semantic decoding or hidden context conversion is
  used.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextShift
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacy
  RawCodedProofAtomicAdequacyStandard
  RawCodedProofAllIConstructor
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation
  RawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph
  RawCodedPAAxiomContextSelfShift
  RawCodedRestrictedPAConsistencyOpenDescent
  RawCodedRestrictedPAConsistencyTripleExDescent
  RawCodedRestrictedPAConsistencyShiftOrbit
  RawCodedRestrictedPAConsistencyShiftRealization
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPAProof
  RawCodedRestrictedTargetTemplateContext
  RawCodedTemplateSyntax
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedDynamicContextTruthSelector
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.

Module
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessLeafRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeAxiomSoundnessPositiveGraph.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedRestrictedPAConsistencyOpenDescent.
Import PABoundedRawCodedRestrictedPAConsistencyTripleExDescent.
Import PABoundedRawCodedRestrictedPAConsistencyShiftOrbit.
Import PABoundedRawCodedRestrictedPAConsistencyShiftRealization.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalBridgeFieldsHeadAdequacy.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedDynamicContextTruthSelector.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectCoherenceLink.

(** ------------------------------------------------------------------
    A generic proof-producing shell for two universals and three arrows. *)

Definition rawPALocalProofAll2Imp3Root
    (M : RawPAModel)
    (context0 context1 context2
      firstAssumption secondAssumption thirdAssumption target child : M) : M :=
  rawProofAllIRoot M context0
    (rawFormulaAllCode M
      (rawFormulaImpCode M firstAssumption
        (rawFormulaImpCode M secondAssumption
          (rawFormulaImpCode M thirdAssumption target))))
    (rawProofAllIRoot M context1
      (rawFormulaImpCode M firstAssumption
        (rawFormulaImpCode M secondAssumption
          (rawFormulaImpCode M thirdAssumption target)))
      (rawProofImpIRoot M context2 firstAssumption
        (rawFormulaImpCode M secondAssumption
          (rawFormulaImpCode M thirdAssumption target))
        (rawProofImpIRoot M
          (rawListNode M firstAssumption context2) secondAssumption
          (rawFormulaImpCode M thirdAssumption target)
          (rawProofImpIRoot M
            (rawListNode M secondAssumption
              (rawListNode M firstAssumption context2))
            thirdAssumption target child)))).

Arguments rawPALocalProofAll2Imp3Root
  M context0 context1 context2 firstAssumption secondAssumption
    thirdAssumption target child : clear implicits.

(** Every node outside [child] is forced by the displayed logical shell.
    Thus this theorem removes all proof-tree work from the later represented
    synchronized traversal. *)
Theorem raw_codedPALocalProofOf_all2_imp3_shell : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context0 context1 context2
      firstAssumption secondAssumption thirdAssumption target child,
  RawContextShift M context0 context1 ->
  RawContextShift M context1 context2 ->
  RawCodedPALocalProofOf M
    (rawListNode M thirdAssumption
      (rawListNode M secondAssumption
        (rawListNode M firstAssumption context2)))
    target child ->
  RawCodedPALocalProofOf M context0
    (rawFormulaAllCode M (rawFormulaAllCode M
      (rawFormulaImpCode M firstAssumption
        (rawFormulaImpCode M secondAssumption
          (rawFormulaImpCode M thirdAssumption target)))))
    (rawPALocalProofAll2Imp3Root M context0 context1 context2
      firstAssumption secondAssumption thirdAssumption target child).
Proof.
  intros M hPA context0 context1 context2
    firstAssumption secondAssumption thirdAssumption target child
    hshift01 hshift12 hchild.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawListNode M secondAssumption
      (rawListNode M firstAssumption context2))
    thirdAssumption target child hchild) as hthird.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawListNode M firstAssumption context2)
    secondAssumption (rawFormulaImpCode M thirdAssumption target)
    (rawProofImpIRoot M
      (rawListNode M secondAssumption
        (rawListNode M firstAssumption context2))
      thirdAssumption target child) hthird) as hsecond.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    context2 firstAssumption
    (rawFormulaImpCode M secondAssumption
      (rawFormulaImpCode M thirdAssumption target))
    (rawProofImpIRoot M
      (rawListNode M firstAssumption context2) secondAssumption
      (rawFormulaImpCode M thirdAssumption target)
      (rawProofImpIRoot M
        (rawListNode M secondAssumption
          (rawListNode M firstAssumption context2))
        thirdAssumption target child)) hsecond) as hfirst.
  destruct hfirst as [hfirstCoverage hfirstEndpoint].
  pose proof (raw_proofAllI_ruleCoverage M hPA
    context1 context2
    (rawFormulaImpCode M firstAssumption
      (rawFormulaImpCode M secondAssumption
        (rawFormulaImpCode M thirdAssumption target)))
    (rawProofImpIRoot M context2 firstAssumption
      (rawFormulaImpCode M secondAssumption
        (rawFormulaImpCode M thirdAssumption target))
      (rawProofImpIRoot M
        (rawListNode M firstAssumption context2) secondAssumption
        (rawFormulaImpCode M thirdAssumption target)
        (rawProofImpIRoot M
          (rawListNode M secondAssumption
            (rawListNode M firstAssumption context2))
          thirdAssumption target child)))
    hshift12 hfirstCoverage hfirstEndpoint) as hinnerCoverage.
  pose proof (raw_proofAllI_endpoint M context1
    (rawFormulaImpCode M firstAssumption
      (rawFormulaImpCode M secondAssumption
        (rawFormulaImpCode M thirdAssumption target)))
    (rawProofImpIRoot M context2 firstAssumption
      (rawFormulaImpCode M secondAssumption
        (rawFormulaImpCode M thirdAssumption target))
      (rawProofImpIRoot M
        (rawListNode M firstAssumption context2) secondAssumption
        (rawFormulaImpCode M thirdAssumption target)
        (rawProofImpIRoot M
          (rawListNode M secondAssumption
            (rawListNode M firstAssumption context2))
          thirdAssumption target child)))) as hinnerEndpoint.
  split.
  - exact (raw_proofAllI_ruleCoverage M hPA
      context0 context1
      (rawFormulaAllCode M
        (rawFormulaImpCode M firstAssumption
          (rawFormulaImpCode M secondAssumption
            (rawFormulaImpCode M thirdAssumption target))))
      (rawProofAllIRoot M context1
        (rawFormulaImpCode M firstAssumption
          (rawFormulaImpCode M secondAssumption
            (rawFormulaImpCode M thirdAssumption target)))
        (rawProofImpIRoot M context2 firstAssumption
          (rawFormulaImpCode M secondAssumption
            (rawFormulaImpCode M thirdAssumption target))
          (rawProofImpIRoot M
            (rawListNode M firstAssumption context2) secondAssumption
            (rawFormulaImpCode M thirdAssumption target)
            (rawProofImpIRoot M
              (rawListNode M secondAssumption
                (rawListNode M firstAssumption context2))
              thirdAssumption target child))))
      hshift01 hinnerCoverage hinnerEndpoint).
  - exact (raw_proofAllI_endpoint M context0
      (rawFormulaAllCode M
        (rawFormulaImpCode M firstAssumption
          (rawFormulaImpCode M secondAssumption
            (rawFormulaImpCode M thirdAssumption target))))
      (rawProofAllIRoot M context1
        (rawFormulaImpCode M firstAssumption
          (rawFormulaImpCode M secondAssumption
            (rawFormulaImpCode M thirdAssumption target)))
        (rawProofImpIRoot M context2 firstAssumption
          (rawFormulaImpCode M secondAssumption
            (rawFormulaImpCode M thirdAssumption target))
          (rawProofImpIRoot M
            (rawListNode M firstAssumption context2) secondAssumption
            (rawFormulaImpCode M thirdAssumption target)
            (rawProofImpIRoot M
              (rawListNode M secondAssumption
                (rawListNode M firstAssumption context2))
              thirdAssumption target child))))).
Qed.

(** ------------------------------------------------------------------
    Exact subformula codes of selected native context truth. *)

Definition rawCoqRestrictedPANativeAxiomContextWitnessCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    (embedPAFormula
      (codedPAAxiomWitnessContextTermAt (tVar 1) (tVar 0))).

Definition rawCoqRestrictedPANativeAxiomContextBoundedCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    (restrictedTargetTemplateFormulaContext
      coqRestrictedPASoundnessLowerLevelTerm
      (restrictedTargetContextAllBoundedContext (tVar 0))).

Definition rawCoqRestrictedPANativeAxiomContextAdequacyCode
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : M :=
  rawDirectTemplateFormula inputs
    (embedPAFormula (contextAllAtomicallyAdequateTermAt (tVar 0))).

Definition rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
    (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (nextGlobalSigma : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)) : M :=
  rawTernaryApplicationOutput contextApplicationSelector
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters ttZero)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters ttZero)
    (rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters (ttVar 0)).

Arguments rawCoqRestrictedPANativeAxiomContextWitnessCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPANativeAxiomContextBoundedCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPANativeAxiomContextAdequacyCode M inputs
  : clear implicits.
Arguments rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
  M parameters nextGlobalSigma sigmaApplicationSelector
    contextApplicationSelector : clear implicits.

Lemma rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode_shell_view :
  forall (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    nextGlobalSigma
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)),
  rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector =
  rawFormulaAllCode M (rawFormulaAllCode M
    (rawFormulaImpCode M
      (rawCoqRestrictedPANativeAxiomContextWitnessCode M inputs)
      (rawFormulaImpCode M
        (rawCoqRestrictedPANativeAxiomContextBoundedCode M inputs)
        (rawFormulaImpCode M
          (rawCoqRestrictedPANativeAxiomContextAdequacyCode M inputs)
          (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
            M parameters nextGlobalSigma sigmaApplicationSelector
            contextApplicationSelector))))).
Proof.
  intros. reflexivity.
Qed.

(** ------------------------------------------------------------------
    The sharp synchronized-list residual. *)

(** The only requested proof is the selected context leaf after both
    eigenvariable shifts and after adjoining the three hypotheses in their
    actual implication-introduction order.  The native link prevents this
    compiler from choosing an unrelated context predicate or axiom field. *)
Definition RawCoqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler
    (M : RawPAModel) : Prop :=
  forall (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    context0 context1 context2,
  RawCoqRestrictedPANativeAxiomContextTruthLinkAt
    M parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    contextApplicationSelector ->
  RawContextShift M
    (rawListNode M nextAxiomSoundness context0) context1 ->
  RawContextShift M context1 context2 ->
  exists leafRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M
        (rawCoqRestrictedPANativeAxiomContextAdequacyCode M inputs)
        (rawListNode M
          (rawCoqRestrictedPANativeAxiomContextBoundedCode M inputs)
          (rawListNode M
            (rawCoqRestrictedPANativeAxiomContextWitnessCode M inputs)
            context2)))
      (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
        M parameters nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      leafRoot.

Arguments RawCoqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler
  M : clear implicits.

(** Pointwise reconstruction of the old body obligation.  The conclusion is
    exactly the selected native direct code, not merely an extensionally
    equivalent formula. *)
Theorem raw_coqRestrictedPANativeAxiomContextTruthBodyRoot_of_traversal_leaf :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    context0 context1 context2,
  RawCoqRestrictedPANativeAxiomContextTruthLinkAt
    M parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    contextApplicationSelector ->
  RawContextShift M
    (rawListNode M nextAxiomSoundness context0) context1 ->
  RawContextShift M context1 context2 ->
  (exists leafRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M
        (rawCoqRestrictedPANativeAxiomContextAdequacyCode M inputs)
        (rawListNode M
          (rawCoqRestrictedPANativeAxiomContextBoundedCode M inputs)
          (rawListNode M
            (rawCoqRestrictedPANativeAxiomContextWitnessCode M inputs)
            context2)))
      (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
        M parameters nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      leafRoot) ->
  exists bodyRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M nextAxiomSoundness context0)
      (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
        M parameters inputs nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      bodyRoot.
Proof.
  intros M hPA parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    context0 context1 context2 _ hshift01 hshift12
    [leafRoot hleaf].
  exists (rawPALocalProofAll2Imp3Root M
    (rawListNode M nextAxiomSoundness context0) context1 context2
    (rawCoqRestrictedPANativeAxiomContextWitnessCode M inputs)
    (rawCoqRestrictedPANativeAxiomContextBoundedCode M inputs)
    (rawCoqRestrictedPANativeAxiomContextAdequacyCode M inputs)
    (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
      M parameters nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector)
    leafRoot).
  rewrite
    rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode_shell_view.
  exact (raw_codedPALocalProofOf_all2_imp3_shell M hPA
    (rawListNode M nextAxiomSoundness context0) context1 context2
    (rawCoqRestrictedPANativeAxiomContextWitnessCode M inputs)
    (rawCoqRestrictedPANativeAxiomContextBoundedCode M inputs)
    (rawCoqRestrictedPANativeAxiomContextAdequacyCode M inputs)
    (rawCoqRestrictedPANativeAxiomContextSelectedLeafCode
      M parameters nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector)
    leafRoot hshift01 hshift12 hleaf).
Qed.

(** ------------------------------------------------------------------
    Generate the two eigenvariable shifts from syntax adequacy. *)

(** All three opaque-looking children of the selected axiom field are
    targets of represented syntax operations in the native link.  Their
    atomic adequacy therefore follows from those very operation traces; no
    semantic truth assumption is involved. *)
Lemma raw_coqRestrictedPANativeAxiomContextTruthLink_axiom_adequate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector)),
  RawCoqRestrictedPANativeAxiomContextTruthLinkAt
    M parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    contextApplicationSelector ->
  RawCodedFormulaAtomicallyAdequate M nextAxiomSoundness.
Proof.
  intros M hPA parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector hlink.
  destruct hlink as
    [_ (currentLevel & currentLevelNumeral & _ & _ & hnumeral &
      hsigmaDomain & hpiDomain & hnextSigma & _ & hfield & _ & _ & _)].
  rewrite hfield.
  apply (rawDynamicTruthNativeAxiomSoundnessFieldCode_atomically_adequate
    M hPA).
  - exact (raw_dynamicTruthNativeAxiomDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthNativeAxiomSigmaDomainTemplate)
      sigmaDomain hnumeral hsigmaDomain).
  - exact (raw_dynamicTruthNativeAxiomDomain_target_atomically_adequate
      M hPA currentLevel currentLevelNumeral
      (formulaCode dynamicTruthNativeAxiomPiDomainTemplate)
      piDomain hnumeral hpiDomain).
  - exact
      (raw_dynamicTruthNativeAxiomApplication_target_atomically_adequate
        M hPA nextGlobalSigma nextSigmaEvidence hnextSigma).
Qed.

(** This is the natural well-formed-context variant of the earlier body
    compiler.  Unlike the original arbitrary-tail interface, it exposes the
    precise condition needed by represented universal introduction. *)
Definition
    RawCoqRestrictedPANativeAxiomContextTruthAdequateBodyRootCompiler
    (M : RawPAModel) : Prop :=
  forall (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : nat -> M)
    predecessorLevel currentGlobalSigma currentGlobalPi
    sigmaDomain piDomain nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (contextApplicationSelector :
      RawCodedTernaryApplicationSelector M
        (rawDynamicContextAllSigmaCode sigmaApplicationSelector))
    context,
  RawCoqRestrictedPANativeAxiomContextTruthLinkAt
    M parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    contextApplicationSelector ->
  RawContextAllAtomicallyAdequate M context ->
  exists bodyRoot : M,
    RawCodedPALocalProofOf M
      (rawListNode M nextAxiomSoundness context)
      (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
        M parameters inputs nextGlobalSigma sigmaApplicationSelector
        contextApplicationSelector)
      bodyRoot.

Arguments
  RawCoqRestrictedPANativeAxiomContextTruthAdequateBodyRootCompiler
  M : clear implicits.

(** Once the synchronized traversal leaf is available, both binder shifts
    are constructed internally.  Atomic adequacy of the first shifted
    context is a theorem about every [RawContextShift] target, so no second
    premise has to be supplied by the caller. *)
Theorem
    raw_coqRestrictedPANativeAxiomContextTruthAdequateBodyRootCompiler_of_leaf
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawCoqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler M ->
  RawCoqRestrictedPANativeAxiomContextTruthAdequateBodyRootCompiler M.
Proof.
  intros M hPA hleafCompiler parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector context
    hlink hcontextAdequate.
  pose proof
    (raw_coqRestrictedPANativeAxiomContextTruthLink_axiom_adequate
      M hPA parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector hlink)
    as haxiomAdequate.
  pose proof (raw_contextAllAtomicallyAdequate_cons M hPA
    context nextAxiomSoundness hcontextAdequate haxiomAdequate)
    as hsourceAdequate.
  destruct (raw_contextShift_exists_of_all_atomically_adequate M hPA
    (rawListNode M nextAxiomSoundness context) hsourceAdequate)
    as [context1 hshift01].
  pose proof (raw_contextShift_target_all_atomically_adequate M hPA
    (rawListNode M nextAxiomSoundness context) context1 hshift01)
    as hcontext1Adequate.
  destruct (raw_contextShift_exists_of_all_atomically_adequate M hPA
    context1 hcontext1Adequate) as [context2 hshift12].
  destruct (hleafCompiler parameters inputs tail predecessorLevel
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    context context1 context2 hlink hshift01 hshift12)
    as [leafRoot hleaf].
  exact
    (raw_coqRestrictedPANativeAxiomContextTruthBodyRoot_of_traversal_leaf
      M hPA parameters inputs tail predecessorLevel
      currentGlobalSigma currentGlobalPi sigmaDomain piDomain
      nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector contextApplicationSelector
      context context1 context2 hlink hshift01 hshift12
      (ex_intro _ leafRoot hleaf)).
Qed.

(** ------------------------------------------------------------------
    Specialization to the final consistency bridge. *)

(** The final bridge context is not an arbitrary carrier number.  Its base
    is a witnessed PA context, its three binder shifts are represented by
    the restricted-proof descent orbit, and its fields head is atomically
    adequate by the numeral trace.  We expose the resulting context
    adequacy because it is exactly what universal introduction needs. *)
Lemma raw_dynamicTruthNativeFinal_bridge_context_all_atomically_adequate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext,
  RawDynamicTruthNativeFinalStagedGraphTraceAt M tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode ->
  RawDynamicTruthNativeFinalStagedPrerequisitesOn M
    witnessList baseContext
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution
    nextAxiomSoundness ->
  RawContextAllAtomicallyAdequate M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode baseContext).
Proof.
  intros M hPA tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    htrace hprerequisites.
  pose proof htrace as htraceCopy.
  destruct htraceCopy as [_ _ _ _ _ _ _ hsource].
  destruct hsource as [_ hnumeral _ _].
  pose proof hprerequisites as hprerequisitesCopy.
  destruct hprerequisitesCopy as
    (currentLocalRoot & currentCrossLevelRoot & currentShiftRoot &
      currentSubstitutionRoot & currentAxiomSoundnessRoot & currentFinalRoot &
      nextLocalRoot & nextCrossLevelRoot & nextShiftRoot &
      nextSubstitutionRoot & nextAxiomSoundnessRoot &
      [hprefix _]).
  destruct hprefix as [hwitness _ _ _ _ _ _ _ _ _ _].
  assert (hbaseShift : RawContextShift M baseContext baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_selfShift M hPA
      witnessList baseContext hwitness).
  }
  set (shiftedRootContext :=
    rawRestrictedPACanonicalShiftedRootContextCode
      M baseContext successorNumeralCode).
  set (shiftedWitnessContext :=
    rawRestrictedPACanonicalShiftedWitnessContextCode
      M baseContext successorNumeralCode).
  set (shiftedProofContext :=
    rawRestrictedPACanonicalShiftedProofContextCode
      M baseContext successorNumeralCode).
  assert (hcontexts : RawRestrictedPAExistentialDescentContexts M
      successorNumeralCode baseContext shiftedRootContext
      shiftedWitnessContext shiftedProofContext).
  {
    unfold shiftedRootContext, shiftedWitnessContext, shiftedProofContext.
    exact (raw_restrictedPAExistentialDescentContexts_realized
      M hPA (raw_succ M level) successorNumeralCode baseContext
      hnumeral hbaseShift).
  }
  destruct hcontexts as [_ [_ hproofShift]].
  pose proof (raw_contextShift_target_all_atomically_adequate M hPA
    (rawRestrictedPAAfterProofContextCode M successorNumeralCode
      shiftedWitnessContext)
    shiftedProofContext hproofShift) as hshiftedProofAdequate.
  pose proof
    (raw_dynamicTruthNativeFinalBridgeFieldsHeadAdequacyCompiler M hPA
      tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites) as hfieldsAdequate.
  unfold rawCoqRestrictedPAConsistencyBridgeContextCode,
    rawRestrictedPAFieldsContextCode.
  exact (raw_contextAllAtomicallyAdequate_cons M hPA
    shiftedProofContext
    (rawRestrictedPAProofFieldsCode M successorNumeralCode)
    hshiftedProofAdequate hfieldsAdequate).
Qed.

(** This is the final compiler adapter with the residual reduced to the
    synchronized traversal leaf.  In particular, neither universal-binder
    shifts, the three implication introductions, nor bridge-context syntax
    adequacy remain assumptions. *)
Theorem
    raw_dynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler_of_traversal_leaf
    : forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPANativeAxiomContextTruthTraversalLeafCompiler M ->
  RawDynamicTruthNativeFinalSelectedAxiomContextTruthRootCompiler M inputs.
Proof.
  intros M hPA inputs hleafCompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    parameters currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    htrace hprerequisites _ hlink.
  pose proof
    (raw_dynamicTruthNativeFinal_bridge_context_all_atomically_adequate
      M hPA tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      htrace hprerequisites) as hbridgeAdequate.
  pose proof
    (raw_coqRestrictedPANativeAxiomContextTruthAdequateBodyRootCompiler_of_leaf
      M hPA hleafCompiler) as hbodyCompiler.
  destruct (hbodyCompiler parameters inputs tail level
    currentGlobalSigma currentGlobalPi sigmaDomain piDomain
    nextSigmaEvidence nextAxiomSoundness nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector contextApplicationSelector
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode baseContext)
    hlink hbridgeAdequate) as [bodyRoot hbody].
  exists (rawProofImpIRoot M
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode baseContext)
    nextAxiomSoundness
    (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector)
    bodyRoot).
  exact (raw_codedPALocalProofOf_impI M hPA
    (rawCoqRestrictedPAConsistencyBridgeContextCode
      M successorNumeralCode baseContext)
    nextAxiomSoundness
    (rawCoqRestrictedPASelectedAxiomContextsTruthDirectCode
      M parameters inputs nextGlobalSigma sigmaApplicationSelector
      contextApplicationSelector)
    bodyRoot hbody).
Qed.

End
  PABoundedRawCodedRestrictedPAAxiomContextTruthNativeDirectBodyShell.
