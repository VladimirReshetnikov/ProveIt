(**
  Reduce the selected successor-Sigma bottom law to seven local cases.

  The public bottom-law seam names an application of a graph-selected global
  Sigma predicate at three *quoted terms*: the term computing the code of
  bottom and two zero terms.  A paired-successor edge determines the local
  Sigma row hidden below that global ten-witness wrapper.  This file first
  records that exact normalization, including the lower-Pi application chosen
  by the same edge and selector.

  What remains is deliberately proof-theoretic and finite.  Under a temporary
  assumption of the selected global application, a producer supplies:

  - the right-associated disjunction of the seven local Sigma constructors;
  - one implication from each named constructor branch to bottom; and
  - exactly the context/atomic-adequacy resources consumed by the published
    derived finite-disjunction eliminator.

  The eliminator produces bottom in the temporary context and implication
  introduction discharges the selected application.  Thus the residual does
  not ask for a proof of an opaque arbitrary conclusion.  In particular, the
  guarded Sigma/Or append producer supplies only the fifth positive branch of
  this list; it cannot by itself be specialized to the bottom refutation.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionDerivedCases
  RawCodedTemplateNumeralParameters
  RawCodedTemplateTernaryApplication
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalSigmaTernaryApplicationView
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthNativeFinalStagedRootCompilation
  RawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector
  RawCodedRestrictedPABottomTruthNativeDirectRefutationLink.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPASelectedSigmaBottomSevenCaseReduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionDerivedCases.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalSigmaTernaryApplicationView.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessConclusionTruthDirectSelector.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedDynamicTruthNativeFinalStagedRootCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeFinalGrowingUniversalSoundnessBridgeDirect.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import PABoundedRawCodedRestrictedPABottomTruthNativeDirectRefutationLink.

(** ------------------------------------------------------------------
    Exact application and successor-row normalization. *)

Definition rawCoqRestrictedPASelectedSigmaBottomApplicationCode
    (M : RawPAModel) (nextGlobalSigma : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma) : M :=
  rawTernaryApplicationOutput sigmaApplicationSelector
    (rawQuotedTermCode M rawFormulaBotCodeTerm)
    (rawQuotedTermCode M tZero)
    (rawQuotedTermCode M tZero).

Arguments rawCoqRestrictedPASelectedSigmaBottomApplicationCode
  M nextGlobalSigma sigmaApplicationSelector : clear implicits.

Definition rawCoqRestrictedPASelectedSigmaBottomAssumptionContextCode
    (M : RawPAModel) (nextGlobalSigma : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (context : M) : M :=
  rawListNode M
    (rawCoqRestrictedPASelectedSigmaBottomApplicationCode
      M nextGlobalSigma sigmaApplicationSelector)
    context.

Arguments rawCoqRestrictedPASelectedSigmaBottomAssumptionContextCode
  M nextGlobalSigma sigmaApplicationSelector context : clear implicits.

(** The expanded local row hidden below the selected global application.
    [lowerLevel] is the level argument of the paired successor itself.  In
    the native bottom link it is [succ predecessorLevel], so [upperNumeral]
    codes its successor. *)
Definition RawCoqRestrictedPASelectedSigmaBottomExposedRowAt
    (M : RawPAModel)
    (currentGlobalSigma currentGlobalPi lowerLevel
      nextGlobalSigma nextGlobalPi : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (lowerPiApplication : M) : Prop :=
  exists localSigma localPi upperNumeral domain : M,
    RawNumeralTermCodeAt M (raw_succ M lowerLevel) upperNumeral /\
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode) domain /\
    RawDynamicTruthCoqLowerApplication M
      currentGlobalPi lowerPiApplication /\
    localSigma = rawDynamicTruthSigmaSuccessorRowCode M
      domain lowerPiApplication /\
    RawDynamicTruthPiSuccessorRowAt M
      currentGlobalSigma lowerLevel localPi /\
    nextGlobalSigma = rawDynamicTruthGlobalFormulaCode M
      tZero localSigma localPi /\
    nextGlobalPi = rawDynamicTruthGlobalFormulaCode M
      (Term.numeral 1) localSigma localPi /\
    RawCodedTernaryApplication M
      (rawDynamicTruthGlobalFormulaCode M tZero localSigma localPi)
      (rawQuotedTermCode M rawFormulaBotCodeTerm)
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero)
      (rawCoqRestrictedPASelectedSigmaBottomApplicationCode
        M nextGlobalSigma sigmaApplicationSelector).

Arguments RawCoqRestrictedPASelectedSigmaBottomExposedRowAt
  M currentGlobalSigma currentGlobalPi lowerLevel
  nextGlobalSigma nextGlobalPi sigmaApplicationSelector
  lowerPiApplication : clear implicits.

(** The successor/selector link determines an exposed lower-Pi application.
    This is graph normalization only; no semantic truth is converted into a
    represented PA proof. *)
Theorem raw_coqRestrictedPASelectedSigmaBottom_exposed_row_of_native_link :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (parameters : RawCodedTemplateNumeralParameters M)
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      currentGlobalSigma currentGlobalPi predecessorLevel
      nextGlobalSigma nextGlobalPi
      (sigmaApplicationSelector :
        RawCodedTernaryApplicationSelector M nextGlobalSigma),
  RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
    M parameters inputs currentGlobalSigma currentGlobalPi predecessorLevel
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector ->
  exists lowerPiApplication : M,
    RawCoqRestrictedPASelectedSigmaBottomExposedRowAt M
      currentGlobalSigma currentGlobalPi (raw_succ M predecessorLevel)
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      lowerPiApplication.
Proof.
  intros M hPA parameters inputs currentGlobalSigma currentGlobalPi
    predecessorLevel nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    hlink.
  destruct hlink as [hsuccessor [_hdeep _hselectorLink]].
  pose proof
    (raw_dynamicTruthGlobalSigmaTernaryApplication_selector_view
      M currentGlobalSigma currentGlobalPi (raw_succ M predecessorLevel)
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      (rawQuotedTermCode M rawFormulaBotCodeTerm)
      (rawQuotedTermCode M tZero) (rawQuotedTermCode M tZero)
      hsuccessor
      (raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax
        M hPA rawFormulaBotCodeTerm)
      (raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax M hPA tZero)
      (raw_coqRestrictedPAConclusionTruth_quotedTerm_syntax M hPA tZero))
    as hview.
  destruct
    (raw_dynamicTruthGlobalSigmaTernaryApplication_view_exposes_sigma_row
      M currentGlobalSigma currentGlobalPi
      (raw_succ M predecessorLevel) nextGlobalSigma nextGlobalPi
      (rawQuotedTermCode M rawFormulaBotCodeTerm)
      (rawQuotedTermCode M tZero) (rawQuotedTermCode M tZero)
      (rawCoqRestrictedPASelectedSigmaBottomApplicationCode
        M nextGlobalSigma sigmaApplicationSelector)
      hview)
    as (localSigma & localPi & upperNumeral & domain & lowerPiApplication &
      hnumeral & hdomain & hlower & hlocalSigma & hlocalPi &
      hnextSigma & hnextPi & happlication).
  exists lowerPiApplication, localSigma, localPi, upperNumeral, domain.
  repeat split; assumption.
Qed.

(** ------------------------------------------------------------------
    The exact seven proof-producing residuals. *)

(** The finite list used by the generic eliminator is definitionally the
    native Or7 row. *)
Lemma rawDynamicTruthLocalSigmaBranches_right_disjunction : forall
    (M : RawPAModel) lowerPiApplication,
  rawFiniteRightDisjunctionCode M
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication) =
  rawDynamicTruthLocalSigmaOr7Code M lowerPiApplication.
Proof. reflexivity. Qed.

(** The synchronized guarded append producer constructs this one positive
    *unspecialized* alternative.  The lemma makes its exact position explicit:
    it is a member of the seven-way row, not a proof of the row's negation. *)
Lemma rawDynamicTruthLocalSigmaOr_branch_in_branches : forall
    (M : RawPAModel) lowerPiApplication,
  In (rawDynamicTruthSigmaOrEx8BranchCode M)
    (rawDynamicTruthLocalSigmaBranches M lowerPiApplication).
Proof.
  intros M lowerPiApplication.
  unfold rawDynamicTruthLocalSigmaBranches,
    dynamicTruthLocalSigmaBranchOrder.
  cbn [map rawDynamicTruthLocalSigmaBranchCode].
  right. right. right. right. left. reflexivity.
Qed.

(** Every branch still has the three public truth arguments free.  Applying
    the global predicate at bottom/zero/zero therefore does not expose the
    raw branch codes above, but seven outputs of the same represented ternary
    operation.  Keeping the traces in this record prevents the subtle but
    invalid replacement of specialized branches by their open sources. *)
Record RawCoqRestrictedPASelectedSigmaBottomAppliedBranchesAt
    (M : RawPAModel) (lowerPiApplication : M) : Type := {
  rawCoqRestrictedPASelectedSigmaBottom_branchApplicationCode :
    DynamicTruthLocalSigmaBranch -> M;
  rawCoqRestrictedPASelectedSigmaBottom_branchApplicationTrace :
    forall branch : DynamicTruthLocalSigmaBranch,
      RawCodedTernaryApplication M
        (rawDynamicTruthLocalSigmaBranchCode
          M lowerPiApplication branch)
        (rawQuotedTermCode M rawFormulaBotCodeTerm)
        (rawQuotedTermCode M tZero)
        (rawQuotedTermCode M tZero)
        (rawCoqRestrictedPASelectedSigmaBottom_branchApplicationCode
          branch)
}.

Arguments RawCoqRestrictedPASelectedSigmaBottomAppliedBranchesAt
  M lowerPiApplication : clear implicits.
Arguments rawCoqRestrictedPASelectedSigmaBottom_branchApplicationCode
  {M lowerPiApplication} _ branch.

Definition rawCoqRestrictedPASelectedSigmaBottomAppliedBranches
    (M : RawPAModel) (lowerPiApplication : M)
    (applications :
      RawCoqRestrictedPASelectedSigmaBottomAppliedBranchesAt
        M lowerPiApplication) : list M :=
  map
    (rawCoqRestrictedPASelectedSigmaBottom_branchApplicationCode
      applications)
    dynamicTruthLocalSigmaBranchOrder.

Arguments rawCoqRestrictedPASelectedSigmaBottomAppliedBranches
  M lowerPiApplication applications : clear implicits.

(** The guarded Sigma/Or output remains exactly the fifth alternative after
    specialization, but obtaining it requires the corresponding application
    trace stored above. *)
Lemma rawCoqRestrictedPASelectedSigmaBottom_or_application_in_branches :
    forall (M : RawPAModel) lowerPiApplication
      (applications :
        RawCoqRestrictedPASelectedSigmaBottomAppliedBranchesAt
          M lowerPiApplication),
  In
    (rawCoqRestrictedPASelectedSigmaBottom_branchApplicationCode
      applications DTLocalSigmaOr)
    (rawCoqRestrictedPASelectedSigmaBottomAppliedBranches
      M lowerPiApplication applications).
Proof.
  intros M lowerPiApplication applications.
  unfold rawCoqRestrictedPASelectedSigmaBottomAppliedBranches,
    dynamicTruthLocalSigmaBranchOrder.
  cbn [map].
  right. right. right. right. left. reflexivity.
Qed.

(** Proof roots after assuming the selected global application.  The row
    root is the concrete output of global-wrapper and local-row traversal.
    The case roots are the seven constructor-specific bottom implications.
    The resource field contains only what recursive Or-E transports consume. *)
Record RawCoqRestrictedPASelectedSigmaBottomSevenCaseProofSupportAt
    (M : RawPAModel) (nextGlobalSigma : M)
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    (context lowerPiApplication : M)
    (applications :
      RawCoqRestrictedPASelectedSigmaBottomAppliedBranchesAt
        M lowerPiApplication) : Prop := {
  rawCoqRestrictedPASelectedSigmaBottom_caseResources :
    RawFiniteDisjunctionDerivedCaseResources M
      (rawCoqRestrictedPASelectedSigmaBottomAppliedBranches
        M lowerPiApplication applications)
      (rawCoqRestrictedPASelectedSigmaBottomAssumptionContextCode
        M nextGlobalSigma sigmaApplicationSelector context);
  rawCoqRestrictedPASelectedSigmaBottom_sigmaRowRoot :
    exists sigmaRowRoot : M,
      RawCodedPALocalProofOf M
        (rawCoqRestrictedPASelectedSigmaBottomAssumptionContextCode
          M nextGlobalSigma sigmaApplicationSelector context)
        (rawFiniteRightDisjunctionCode M
          (rawCoqRestrictedPASelectedSigmaBottomAppliedBranches
            M lowerPiApplication applications))
        sigmaRowRoot;
  rawCoqRestrictedPASelectedSigmaBottom_branchRoots :
    forall branch : DynamicTruthLocalSigmaBranch,
      exists branchRoot : M,
        RawCodedPALocalProofOf M
          (rawCoqRestrictedPASelectedSigmaBottomAssumptionContextCode
            M nextGlobalSigma sigmaApplicationSelector context)
          (rawFormulaImpCode M
            (rawCoqRestrictedPASelectedSigmaBottom_branchApplicationCode
              applications branch)
            (rawFormulaBotCode M))
          branchRoot
}.

Arguments RawCoqRestrictedPASelectedSigmaBottomSevenCaseProofSupportAt
  M nextGlobalSigma sigmaApplicationSelector context lowerPiApplication
  applications
  : clear implicits.

(** The complete local reduction.  Notice that its conclusion is the exact
    selected implication used by the public bottom-law link. *)
Theorem raw_coqRestrictedPASelectedSigmaBottom_refutation_of_seven_cases :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      nextGlobalSigma
      (sigmaApplicationSelector :
        RawCodedTernaryApplicationSelector M nextGlobalSigma)
      context lowerPiApplication
      (applications :
        RawCoqRestrictedPASelectedSigmaBottomAppliedBranchesAt
          M lowerPiApplication),
  RawCoqRestrictedPASelectedSigmaBottomSevenCaseProofSupportAt
    M nextGlobalSigma sigmaApplicationSelector context lowerPiApplication
    applications ->
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawCoqRestrictedPASelectedSigmaBottomRefutationCode
        M nextGlobalSigma sigmaApplicationSelector)
      root.
Proof.
  intros M hPA nextGlobalSigma sigmaApplicationSelector
    context lowerPiApplication applications hsupport.
  destruct hsupport as [hresources [sigmaRowRoot hsigmaRow] hbranchRoots].
  set (assumptionContext :=
    rawCoqRestrictedPASelectedSigmaBottomAssumptionContextCode
      M nextGlobalSigma sigmaApplicationSelector context).
  assert (hrow : RawCodedPALocalProofOf M assumptionContext
      (rawFiniteRightDisjunctionCode M
        (rawCoqRestrictedPASelectedSigmaBottomAppliedBranches
          M lowerPiApplication applications))
      sigmaRowRoot).
  { exact hsigmaRow. }
  assert (hcases : RawCodedPALocalFiniteDisjunctionCaseFamily M
      assumptionContext
      (rawCoqRestrictedPASelectedSigmaBottomAppliedBranches
        M lowerPiApplication applications)
      (rawFormulaBotCode M)).
  {
    intros selected hselected.
    unfold rawCoqRestrictedPASelectedSigmaBottomAppliedBranches
      in hselected.
    apply in_map_iff in hselected.
    destruct hselected as [branch [hselected _hinOrder]].
    subst selected.
    exact (hbranchRoots branch).
  }
  destruct
    (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
      M hPA
      (rawCoqRestrictedPASelectedSigmaBottomAppliedBranches
        M lowerPiApplication applications)
      (rawFormulaBotCode M) assumptionContext sigmaRowRoot
      hresources hrow hcases)
    as [bottomRoot hbottom].
  exists (rawProofImpIRoot M context
    (rawCoqRestrictedPASelectedSigmaBottomApplicationCode
      M nextGlobalSigma sigmaApplicationSelector)
    (rawFormulaBotCode M) bottomRoot).
  unfold rawCoqRestrictedPASelectedSigmaBottomRefutationCode,
    rawCoqRestrictedPASelectedSigmaBottomApplicationCode.
  unfold assumptionContext,
    rawCoqRestrictedPASelectedSigmaBottomAssumptionContextCode in hbottom.
  exact (raw_codedPALocalProofOf_impI M hPA context
    (rawTernaryApplicationOutput sigmaApplicationSelector
      (rawQuotedTermCode M rawFormulaBotCodeTerm)
      (rawQuotedTermCode M tZero)
      (rawQuotedTermCode M tZero))
    (rawFormulaBotCode M) bottomRoot hbottom).
Qed.

(** A package-level compiler receives the exact exposed lower-Pi application
    and returns only the finite proof support above. *)
Definition RawCoqRestrictedPASelectedSigmaBottomSevenCaseProofCompiler
    (M : RawPAModel) : Prop :=
  forall (parameters : RawCodedTemplateNumeralParameters M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    currentGlobalSigma currentGlobalPi predecessorLevel
    nextGlobalSigma nextGlobalPi
    (sigmaApplicationSelector :
      RawCodedTernaryApplicationSelector M nextGlobalSigma)
    context lowerPiApplication,
  RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
    M parameters inputs currentGlobalSigma currentGlobalPi predecessorLevel
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector ->
  RawCoqRestrictedPASelectedSigmaBottomExposedRowAt M
    currentGlobalSigma currentGlobalPi (raw_succ M predecessorLevel)
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector
    lowerPiApplication ->
  exists applications :
      RawCoqRestrictedPASelectedSigmaBottomAppliedBranchesAt
        M lowerPiApplication,
    RawCoqRestrictedPASelectedSigmaBottomSevenCaseProofSupportAt
      M nextGlobalSigma sigmaApplicationSelector context lowerPiApplication
      applications.

Arguments RawCoqRestrictedPASelectedSigmaBottomSevenCaseProofCompiler
  M : clear implicits.

(** This is the requested adapter to the historical arbitrary-context seam.
    All mathematical work below the graph normalization is now visible as
    the Or7 projection and seven constructor cases in [ProofSupportAt]. *)
Theorem
    raw_coqRestrictedPASelectedSigmaBottomRefutationRootCompiler_of_seven_cases :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawCoqRestrictedPASelectedSigmaBottomSevenCaseProofCompiler M ->
  RawCoqRestrictedPASelectedSigmaBottomRefutationRootCompiler M.
Proof.
  intros M hPA hcompiler parameters inputs
    currentGlobalSigma currentGlobalPi predecessorLevel
    nextGlobalSigma nextGlobalPi sigmaApplicationSelector context hlink.
  destruct
    (raw_coqRestrictedPASelectedSigmaBottom_exposed_row_of_native_link
      M hPA parameters inputs currentGlobalSigma currentGlobalPi
      predecessorLevel nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector hlink)
    as [lowerPiApplication hexposed].
  destruct
    (hcompiler parameters inputs currentGlobalSigma currentGlobalPi
      predecessorLevel nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector context lowerPiApplication
      hlink hexposed)
    as [applications hsupport].
  exact
    (raw_coqRestrictedPASelectedSigmaBottom_refutation_of_seven_cases
      M hPA nextGlobalSigma sigmaApplicationSelector context
      lowerPiApplication applications hsupport).
Qed.

(** ------------------------------------------------------------------
    Narrow final-context variant.

    The final bridge needs only one known, honestly constructed context.  The
    following interface avoids forcing a growing global-row implementation to
    promise the package-level result for every opaque carrier [context]. *)

Definition
    RawDynamicTruthNativeFinalSelectedSigmaBottomSevenCaseProofCompiler
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  forall (tail : nat -> M) level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
      nextFinal successorNumeralCode witnessList baseContext
      (parameters : RawCodedTemplateNumeralParameters M)
      nativeCurrentGlobalSigma nativeCurrentGlobalPi nativePredecessorLevel
      nextGlobalSigma nextGlobalPi
      (sigmaApplicationSelector :
        RawCodedTernaryApplicationSelector M nextGlobalSigma)
      lowerPiApplication,
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
    rawDirectTemplateTerm inputs
      coqRestrictedPASoundnessLowerLevelTerm = successorNumeralCode ->
    RawCoqRestrictedPANativeSuccessorConclusionTruthSelectorLinkAt
      M parameters inputs nativeCurrentGlobalSigma nativeCurrentGlobalPi
      nativePredecessorLevel nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector ->
    RawCoqRestrictedPASelectedSigmaBottomExposedRowAt M
      nativeCurrentGlobalSigma nativeCurrentGlobalPi
      (raw_succ M nativePredecessorLevel)
      nextGlobalSigma nextGlobalPi sigmaApplicationSelector
      lowerPiApplication ->
    exists applications :
        RawCoqRestrictedPASelectedSigmaBottomAppliedBranchesAt
          M lowerPiApplication,
      RawCoqRestrictedPASelectedSigmaBottomSevenCaseProofSupportAt
        M nextGlobalSigma sigmaApplicationSelector
        (rawCoqRestrictedPAConsistencyBridgeContextCode
          M successorNumeralCode baseContext)
        lowerPiApplication applications.

Arguments
  RawDynamicTruthNativeFinalSelectedSigmaBottomSevenCaseProofCompiler
  M inputs : clear implicits.

Theorem
    raw_dynamicTruthNativeFinalSelectedSigmaBottomRefutationRootCompiler_of_seven_cases :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeFinalSelectedSigmaBottomSevenCaseProofCompiler
    M inputs ->
  RawDynamicTruthNativeFinalSelectedSigmaBottomRefutationRootCompiler
    M inputs.
Proof.
  intros M hPA inputs hcompiler tail level
    currentLocal currentCrossLevel currentShift currentSubstitution
    currentAxiomSoundness currentFinal
    nextLocal nextCrossLevel nextShift nextSubstitution nextAxiomSoundness
    nextFinal successorNumeralCode witnessList baseContext
    parameters nativeCurrentGlobalSigma nativeCurrentGlobalPi
    nativePredecessorLevel nextGlobalSigma nextGlobalPi
    sigmaApplicationSelector htrace hprerequisites hlevel hlink.
  destruct
    (raw_coqRestrictedPASelectedSigmaBottom_exposed_row_of_native_link
      M hPA parameters inputs nativeCurrentGlobalSigma nativeCurrentGlobalPi
      nativePredecessorLevel nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector hlink)
    as [lowerPiApplication hexposed].
  destruct
    (hcompiler tail level
      currentLocal currentCrossLevel currentShift currentSubstitution
      currentAxiomSoundness currentFinal
      nextLocal nextCrossLevel nextShift nextSubstitution
      nextAxiomSoundness nextFinal successorNumeralCode
      witnessList baseContext parameters
      nativeCurrentGlobalSigma nativeCurrentGlobalPi
      nativePredecessorLevel nextGlobalSigma nextGlobalPi
      sigmaApplicationSelector lowerPiApplication
      htrace hprerequisites hlevel hlink hexposed)
    as [applications hsupport].
  exact
    (raw_coqRestrictedPASelectedSigmaBottom_refutation_of_seven_cases
      M hPA nextGlobalSigma sigmaApplicationSelector
      (rawCoqRestrictedPAConsistencyBridgeContextCode
        M successorNumeralCode baseContext)
      lowerPiApplication applications hsupport).
Qed.

End
  PABoundedRawCodedRestrictedPASelectedSigmaBottomSevenCaseReduction.
