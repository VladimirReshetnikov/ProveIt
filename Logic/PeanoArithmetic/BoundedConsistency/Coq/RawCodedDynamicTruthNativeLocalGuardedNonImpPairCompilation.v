(**
  Predecessor-free production of every non-conditional collision pair.

  The guarded implication predecessor proves exclusivity only when the
  current parent is an implication.  It therefore cannot soundly discharge
  the conjunction/conjunction or disjunction/disjunction matrix cells.  On
  the other hand, none of the remaining thirty-eight cells depends on any
  predecessor-exclusivity formula: they use the QF theorem, constructor
  disjointness, binder projections, quantifier cross-level roots, or mixed-QF
  replay.

  This module makes that cut precise.  It compiles those thirty-eight pairs
  from the established forty-helper batch and a predecessor-free current
  kernel, then shows that exactly two additional Boolean diagonal pair roots
  complete [RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt].  In
  particular, neither the input records nor their producers mention the
  historical unconditional implication predecessor.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPAAxiomContextSelfShift
  RawCodedTemplatePAEmbedding
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthConstructorBranchDisjointness
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthBinderOffDiagonalExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthQuantifierConditionalCellCompilation
  RawCodedDynamicTruthMixedQFBranchExclusivity
  RawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthNativeLocalLeafRootCompiler
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalRowProjectionCompilation
  RawCodedDynamicTruthNativeLocalGuardedMatrixCompilation
  RawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.
Import PABoundedRawCodedDynamicTruthMixedQFBranchExclusivity.
Import
  PABoundedRawCodedDynamicTruthMixedQFOpaqueQuantifierCellCompilation.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalLeafRootCompiler.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalRowProjectionCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalGuardedMatrixCompilation.
Import
  PABoundedRawCodedDynamicTruthNativeLocalGuardedReducedStagedCompilation.

(** The two Boolean diagonal cells are kept separate from the two guarded
    implication diagonals.  This lets later clients replace their proof
    mechanism independently. *)
Definition DynamicTruthBooleanDiagonalCell
    (sigmaBranch : DynamicTruthLocalSigmaBranch)
    (piBranch : DynamicTruthLocalPiBranch) : Prop :=
  (sigmaBranch = DTLocalSigmaAnd /\ piBranch = DTLocalPiAnd) \/
  (sigmaBranch = DTLocalSigmaOr /\ piBranch = DTLocalPiOr).

Definition DynamicTruthConditionalDiagonalCell
    (sigmaBranch : DynamicTruthLocalSigmaBranch)
    (piBranch : DynamicTruthLocalPiBranch) : Prop :=
  DynamicTruthImpDiagonalCell sigmaBranch piBranch \/
  DynamicTruthBooleanDiagonalCell sigmaBranch piBranch.

(** A pair family with exactly the four constructor-conditional diagonal
    cells removed. *)
Definition RawDynamicTruthLocalCollisionPairFamilyWithoutConditionalAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop :=
  forall sigmaBranch piBranch,
    ~ DynamicTruthConditionalDiagonalCell sigmaBranch piBranch ->
    RawDynamicTruthLocalRootAt M context
      (rawFormulaImpCode M
        (rawDynamicTruthLocalSigmaBranchCode M
          lowerPiApplication sigmaBranch)
        (rawFormulaImpCode M
          (rawDynamicTruthLocalPiBranchCode M
            lowerSigmaApplication piBranch)
          (rawFormulaBotCode M))).

Arguments RawDynamicTruthLocalCollisionPairFamilyWithoutConditionalAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** The exact residual left after the thirty-eight unconditional cells have
    been compiled.  These are completed proofs, not conditional-cell roots,
    so the record does not smuggle in an unguarded predecessor premise. *)
Definition RawDynamicTruthLocalBooleanDiagonalPairRootsAt
    (M : RawPAModel) (context : M) : Prop :=
  RawDynamicTruthLocalRootAt M context
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaAndEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiAndEx8BranchCode M)
        (rawFormulaBotCode M))) /\
  RawDynamicTruthLocalRootAt M context
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaOrEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiOrEx8BranchCode M)
        (rawFormulaBotCode M))).

Arguments RawDynamicTruthLocalBooleanDiagonalPairRootsAt
  M context : clear implicits.

(** Carrier-dependent inputs that cannot be fixed before the current lower
    applications have been selected.  Notice the deliberate absence of any
    predecessor root. *)
Record RawDynamicTruthNativeLocalNonConditionalResidualInputsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop := {
  rawDynamicTruthNativeLocalNonConditional_lowerPiAdequate :
    RawCodedFormulaAtomicallyAdequate M lowerPiApplication;
  rawDynamicTruthNativeLocalNonConditional_lowerSigmaAdequate :
    RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication;
  rawDynamicTruthNativeLocalNonConditional_binderProjections :
    forall cell : DynamicTruthBinderOffDiagonalCell,
      RawDynamicTruthBinderPrincipalProjectionInterfaceAt M context cell
        lowerPiApplication lowerSigmaApplication;
  rawDynamicTruthNativeLocalNonConditional_sigmaExTrace :
    inhabited (RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerSigmaApplication);
  rawDynamicTruthNativeLocalNonConditional_sigmaAllTrace :
    inhabited (RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerPiApplication);
  rawDynamicTruthNativeLocalNonConditional_sigmaExCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
        lowerSigmaApplication);
  rawDynamicTruthNativeLocalNonConditional_sigmaAllCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
        lowerPiApplication);
  rawDynamicTruthNativeLocalNonConditional_mixedReplayRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
}.

Arguments RawDynamicTruthNativeLocalNonConditionalResidualInputsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** Fully assembled inputs for the thirty-eight-cell dispatcher.  This
    intermediate record is useful independently of the native helper batch:
    alternate front ends can supply its roots directly. *)
Record RawDynamicTruthLocalNonConditionalCollisionInputsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop := {
  rawDynamicTruthLocalNonConditional_contextRealizable :
    RawContextListRealizable M context;
  rawDynamicTruthLocalNonConditional_lowerPiAdequate :
    RawCodedFormulaAtomicallyAdequate M lowerPiApplication;
  rawDynamicTruthLocalNonConditional_lowerSigmaAdequate :
    RawCodedFormulaAtomicallyAdequate M lowerSigmaApplication;
  rawDynamicTruthLocalNonConditional_contextSelfShift :
    RawContextShift M context context;
  rawDynamicTruthLocalNonConditional_qfRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthQFEx8BranchExclusivityCode M);
  rawDynamicTruthLocalNonConditional_fixedPairs :
    RawDynamicTruthLocalFixedPairFamily M context
      lowerPiApplication lowerSigmaApplication;
  rawDynamicTruthLocalNonConditional_binderInputs :
    forall cell : DynamicTruthBinderOffDiagonalCell,
      RawDynamicTruthBinderOffDiagonalProofInputsAt M context cell
        lowerPiApplication lowerSigmaApplication;
  rawDynamicTruthLocalNonConditional_sigmaExTrace :
    inhabited (RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerSigmaApplication);
  rawDynamicTruthLocalNonConditional_sigmaAllTrace :
    inhabited (RawDynamicTruthQuantifierLowerApplicationDirectTrace
      M lowerPiApplication);
  rawDynamicTruthLocalNonConditional_sigmaExCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
        lowerSigmaApplication);
  rawDynamicTruthLocalNonConditional_sigmaAllCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
        lowerPiApplication);
  rawDynamicTruthLocalNonConditional_mixedReplayRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFReplayExclusivityCode M);
  rawDynamicTruthLocalNonConditional_mixedCellRoots :
    forall cell : DynamicTruthMixedQFCell,
      RawDynamicTruthLocalRootAt M context
        (rawDynamicTruthMixedQFCellCode M cell
          lowerPiApplication lowerSigmaApplication)
}.

Arguments RawDynamicTruthLocalNonConditionalCollisionInputsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** The original forty helpers already contain everything fixed that the
    predecessor-free dispatcher needs.  Stating this theorem for the smaller
    batch relaxes the hypothesis; a guarded forty-two-helper wrapper follows
    below. *)
Theorem
    raw_dynamicTruthLocalNonConditionalCollisionInputsAt_of_40_helpers :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList context helperRoots
      lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalNonConditionalResidualInputsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalNonConditionalCollisionInputsAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList context helperRoots
    lowerPi lowerSigma hagreement hwitness hhelpers residual.
  destruct (raw_dynamicTruthNativeLocal_basicCollisionRoots_of_40_helpers
    M hPA translation context helperRoots hagreement hhelpers) as
    (hqf & _himpFalse & _himpTrue & _hand & _hor).
  pose proof
    (raw_dynamicTruthNativeLocal_binderPrincipalRoots_of_40_helpers
      M hPA translation context helperRoots hagreement hhelpers)
    as hbinderPrincipals.
  destruct (rawDynamicTruthNativeLocalNonConditional_sigmaAllTrace
    M context lowerPi lowerSigma residual) as [piTrace].
  destruct (rawDynamicTruthNativeLocalNonConditional_sigmaExTrace
    M context lowerPi lowerSigma residual) as [sigmaTrace].
  pose proof
    (raw_dynamicTruthNativeLocal_mixedQFRoots_of_40_helpers
      M hPA translation witnessList context helperRoots lowerPi lowerSigma
      hagreement hwitness hhelpers
      piTrace sigmaTrace)
    as hmixed.
  refine
    {| rawDynamicTruthLocalNonConditional_contextRealizable :=
         raw_codedPAAxiomWitnessContext_context_realizable
           M witnessList context hwitness;
       rawDynamicTruthLocalNonConditional_lowerPiAdequate :=
         rawDynamicTruthNativeLocalNonConditional_lowerPiAdequate
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalNonConditional_lowerSigmaAdequate :=
         rawDynamicTruthNativeLocalNonConditional_lowerSigmaAdequate
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalNonConditional_contextSelfShift :=
         raw_codedPAAxiomWitnessContext_selfShift
           M hPA witnessList context hwitness;
       rawDynamicTruthLocalNonConditional_qfRoot := hqf;
       rawDynamicTruthLocalNonConditional_fixedPairs :=
         raw_dynamicTruthNativeLocal_fixedPairs_of_40_helpers
           M hPA translation context helperRoots lowerPi lowerSigma
           hagreement hhelpers;
       rawDynamicTruthLocalNonConditional_binderInputs := _;
       rawDynamicTruthLocalNonConditional_sigmaExTrace :=
         inhabits sigmaTrace;
       rawDynamicTruthLocalNonConditional_sigmaAllTrace :=
         inhabits piTrace;
       rawDynamicTruthLocalNonConditional_sigmaExCrossRoot :=
         rawDynamicTruthNativeLocalNonConditional_sigmaExCrossRoot
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalNonConditional_sigmaAllCrossRoot :=
         rawDynamicTruthNativeLocalNonConditional_sigmaAllCrossRoot
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalNonConditional_mixedReplayRoot :=
         rawDynamicTruthNativeLocalNonConditional_mixedReplayRoot
           M context lowerPi lowerSigma residual;
       rawDynamicTruthLocalNonConditional_mixedCellRoots := hmixed |}.
  intro cell. split.
  - exact (rawDynamicTruthNativeLocalNonConditional_binderProjections
      M context lowerPi lowerSigma residual cell).
  - exact (hbinderPrincipals cell).
Qed.

(** Narrow quantifier-diagonal adapters.  The older convenience lemmas take
    the complete collision record, although their proofs inspect only these
    four fields.  Extracting the actual dependency makes the absence of a
    predecessor root kernel-visible. *)
Theorem raw_dynamicTruthLocal_sigmaExPiEx_pair_of_nonconditional_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalNonConditionalCollisionInputsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalRootAt M context
    (rawFormulaImpCode M (rawDynamicTruthSigmaEx8BranchCode M)
      (rawFormulaImpCode M
        (rawDynamicTruthPiExistentialEx8BranchCode M
          lowerSigmaApplication)
        (rawFormulaBotCode M))).
Proof.
  intros M hPA context lowerPi lowerSigma inputs.
  destruct (rawDynamicTruthLocalNonConditional_sigmaExTrace
    M context lowerPi lowerSigma inputs) as [trace].
  destruct (rawDynamicTruthLocalNonConditional_sigmaExCrossRoot
    M context lowerPi lowerSigma inputs) as [premiseRoot hpremise].
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaExPiExConditionalCell_direct
      M hPA context lowerSigma
      trace
      (rawDynamicTruthLocalNonConditional_contextRealizable
        M context lowerPi lowerSigma inputs)
      (rawDynamicTruthLocalNonConditional_contextSelfShift
        M context lowerPi lowerSigma inputs))
    as hcell.
  unfold rawDynamicTruthSigmaExPiExConditionalCellCode in hcell.
  exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
    (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M lowerSigma)
    (rawDynamicTruthSigmaEx8BranchCode M)
    (rawDynamicTruthPiExistentialEx8BranchCode M lowerSigma)
    (rawDynamicTruthSigmaExPiExConditionalCellLocalRoot M hPA context
      lowerSigma trace)
    premiseRoot hcell hpremise).
Qed.

Theorem raw_dynamicTruthLocal_sigmaAllPiAll_pair_of_nonconditional_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalNonConditionalCollisionInputsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalRootAt M context
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaUniversalEx8BranchCode M
        lowerPiApplication)
      (rawFormulaImpCode M (rawDynamicTruthPiAllEx8BranchCode M)
        (rawFormulaBotCode M))).
Proof.
  intros M hPA context lowerPi lowerSigma inputs.
  destruct (rawDynamicTruthLocalNonConditional_sigmaAllTrace
    M context lowerPi lowerSigma inputs) as [trace].
  destruct (rawDynamicTruthLocalNonConditional_sigmaAllCrossRoot
    M context lowerPi lowerSigma inputs) as [premiseRoot hpremise].
  pose proof
    (raw_codedPALocalProofOf_dynamicTruthSigmaAllPiAllConditionalCell_direct
      M hPA context lowerPi
      trace
      (rawDynamicTruthLocalNonConditional_contextRealizable
        M context lowerPi lowerSigma inputs)
      (rawDynamicTruthLocalNonConditional_contextSelfShift
        M context lowerPi lowerSigma inputs))
    as hcell.
  unfold rawDynamicTruthSigmaAllPiAllConditionalCellCode in hcell.
  exact (raw_dynamicTruthLocal_pair_of_conditional M hPA context
    (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M lowerPi)
    (rawDynamicTruthSigmaUniversalEx8BranchCode M lowerPi)
    (rawDynamicTruthPiAllEx8BranchCode M)
    (rawDynamicTruthSigmaAllPiAllConditionalCellLocalRoot M hPA context
      lowerPi trace)
    premiseRoot hcell hpremise).
Qed.

(** Finite dispatcher for the thirty-eight cells.  The four impossible
    branches are rejected from the explicit index predicate before any proof
    resource is selected. *)
Theorem
    raw_dynamicTruthLocalCollisionPairFamilyWithoutConditionalAt_of_inputs :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      context lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalNonConditionalCollisionInputsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutConditionalAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA context lowerPi lowerSigma inputs
    sigmaBranch piBranch hnonconditional.
  destruct sigmaBranch.
  - destruct piBranch.
    + exact (rawDynamicTruthLocalNonConditional_qfRoot
        M context lowerPi lowerSigma inputs).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaQFPiImp).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaQFPiAnd).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaQFPiOr).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaQFPiAll).
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaQFPiEx).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaImpFalseLeftPiQF).
    + exfalso. apply hnonconditional. left. left. now split.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs
        DTSigmaImpFalseLeft DTPiAnd).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs
        DTSigmaImpFalseLeft DTPiOr).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs
        DTSigmaImpFalseLeft DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaImpFalseLeftPiEx
        (rawDynamicTruthLocalNonConditional_contextRealizable
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerPiAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerSigmaAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_binderInputs
          M context lowerPi lowerSigma inputs
          DTBODSigmaImpFalseLeftPiEx)).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaImpTrueRightPiQF).
    + exfalso. apply hnonconditional. left. right. now split.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs
        DTSigmaImpTrueRight DTPiAnd).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs
        DTSigmaImpTrueRight DTPiOr).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs
        DTSigmaImpTrueRight DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaImpTrueRightPiEx
        (rawDynamicTruthLocalNonConditional_contextRealizable
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerPiAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerSigmaAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_binderInputs
          M context lowerPi lowerSigma inputs
          DTBODSigmaImpTrueRightPiEx)).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaAndPiQF).
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaAnd DTPiImp).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exfalso. apply hnonconditional. right. left. now split.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaAnd DTPiOr).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaAnd DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAndPiEx
        (rawDynamicTruthLocalNonConditional_contextRealizable
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerPiAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerSigmaAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_binderInputs
          M context lowerPi lowerSigma inputs DTBODSigmaAndPiEx)).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaOrPiQF).
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaOr DTPiImp).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaOr DTPiAnd).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exfalso. apply hnonconditional. right. right. now split.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaOr DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaOrPiEx
        (rawDynamicTruthLocalNonConditional_contextRealizable
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerPiAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerSigmaAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_binderInputs
          M context lowerPi lowerSigma inputs DTBODSigmaOrPiEx)).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaExPiQF).
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaEx DTPiImp).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaEx DTPiAnd).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaEx DTPiOr).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + apply (rawDynamicTruthLocalNonConditional_fixedPairs
        M context lowerPi lowerSigma inputs DTSigmaEx DTPiAll).
      cbn [DynamicTruthFixedConstructorCell
        DynamicTruthConstructorBranchesDisjoint
        dynamicTruthSigmaBranchPrincipal
        dynamicTruthPiBranchPrincipal].
      repeat split; discriminate.
    + exact
        (raw_dynamicTruthLocal_sigmaExPiEx_pair_of_nonconditional_inputs
          M hPA context lowerPi lowerSigma inputs).
  - destruct piBranch.
    + exact (raw_dynamicTruthLocal_mixedQF_pair M hPA context
        lowerPi lowerSigma
        (rawDynamicTruthLocalNonConditional_mixedReplayRoot
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_mixedCellRoots
          M context lowerPi lowerSigma inputs)
        DTMQFSigmaAllPiQF).
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAllPiImp
        (rawDynamicTruthLocalNonConditional_contextRealizable
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerPiAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerSigmaAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_binderInputs
          M context lowerPi lowerSigma inputs DTBODSigmaAllPiImp)).
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAllPiAnd
        (rawDynamicTruthLocalNonConditional_contextRealizable
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerPiAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerSigmaAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_binderInputs
          M context lowerPi lowerSigma inputs DTBODSigmaAllPiAnd)).
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAllPiOr
        (rawDynamicTruthLocalNonConditional_contextRealizable
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerPiAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerSigmaAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_binderInputs
          M context lowerPi lowerSigma inputs DTBODSigmaAllPiOr)).
    + exact
        (raw_dynamicTruthLocal_sigmaAllPiAll_pair_of_nonconditional_inputs
          M hPA context lowerPi lowerSigma inputs).
    + exact (raw_dynamicTruthLocal_binder_pair M hPA context
        lowerPi lowerSigma DTBODSigmaAllPiEx
        (rawDynamicTruthLocalNonConditional_contextRealizable
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerPiAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_lowerSigmaAdequate
          M context lowerPi lowerSigma inputs)
        (rawDynamicTruthLocalNonConditional_binderInputs
          M context lowerPi lowerSigma inputs DTBODSigmaAllPiEx)).
Qed.

(** Completed partial families weaken along arbitrary witnessed context
    inclusions.  This is stronger than the three-head specialization needed
    by the native exclusive context and avoids recompiling traces after a
    guarded predecessor chooses a larger synchronized witness context. *)
Theorem
    raw_dynamicTruthLocalCollisionPairFamilyWithoutConditionalAt_witnessed_inclusion :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      sourceWitnessList sourceContext targetWitnessList targetContext
      lowerPiApplication lowerSigmaApplication,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M sourceContext targetContext ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutConditionalAt M
    sourceContext lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutConditionalAt M
    targetContext lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA sourceWitnessList sourceContext
    targetWitnessList targetContext lowerPi lowerSigma
    hsource htarget hincluded hfamily sigmaBranch piBranch hnot.
  destruct (hfamily sigmaBranch piBranch hnot) as [root hroot].
  destruct
    (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
      M hPA sourceWitnessList sourceContext targetWitnessList targetContext
      (rawFormulaImpCode M
        (rawDynamicTruthLocalSigmaBranchCode M lowerPi sigmaBranch)
        (rawFormulaImpCode M
          (rawDynamicTruthLocalPiBranchCode M lowerSigma piBranch)
          (rawFormulaBotCode M)))
      root hsource htarget hincluded hroot)
    as [targetRoot htargetRoot].
  now exists targetRoot.
Qed.

Theorem raw_dynamicTruthLocalBooleanDiagonalPairRootsAt_witnessed_inclusion :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      sourceWitnessList sourceContext targetWitnessList targetContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M sourceContext targetContext ->
  RawDynamicTruthLocalBooleanDiagonalPairRootsAt M sourceContext ->
  RawDynamicTruthLocalBooleanDiagonalPairRootsAt M targetContext.
Proof.
  intros M hPA sourceWitnessList sourceContext
    targetWitnessList targetContext hsource htarget hincluded
    [[andRoot hand] [orRoot hor]].
  split.
  - destruct
      (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
        M hPA sourceWitnessList sourceContext
        targetWitnessList targetContext
        (rawFormulaImpCode M
          (rawDynamicTruthSigmaAndEx8BranchCode M)
          (rawFormulaImpCode M
            (rawDynamicTruthPiAndEx8BranchCode M)
            (rawFormulaBotCode M)))
        andRoot hsource htarget hincluded hand)
      as [targetRoot htargetRoot].
    now exists targetRoot.
  - destruct
      (raw_codedPALocalProofWitnessedContextInclusionWeakening_complete
        M hPA sourceWitnessList sourceContext
        targetWitnessList targetContext
        (rawFormulaImpCode M
          (rawDynamicTruthSigmaOrEx8BranchCode M)
          (rawFormulaImpCode M
            (rawDynamicTruthPiOrEx8BranchCode M)
            (rawFormulaBotCode M)))
        orRoot hsource htarget hincluded hor)
      as [targetRoot htargetRoot].
    now exists targetRoot.
Qed.

(** Insert the two Boolean pairs while continuing to omit the two guarded
    implication diagonals. *)
Theorem
    raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_without_conditional_and_boolean :
    forall (M : RawPAModel) context
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalCollisionPairFamilyWithoutConditionalAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalBooleanDiagonalPairRootsAt M context ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M context lowerPi lowerSigma hwithout [hand hor]
    sigmaBranch piBranch hnotImp.
  Ltac use_without_conditional family :=
    apply family;
    unfold DynamicTruthConditionalDiagonalCell,
      DynamicTruthImpDiagonalCell, DynamicTruthBooleanDiagonalCell;
    intros [[[hsigma hpi] | [hsigma hpi]] |
      [[hsigma hpi] | [hsigma hpi]]];
    discriminate.
  destruct sigmaBranch.
  - destruct piBranch; use_without_conditional hwithout.
  - destruct piBranch.
    + use_without_conditional hwithout.
    + exfalso. apply hnotImp. left. now split.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
  - destruct piBranch.
    + use_without_conditional hwithout.
    + exfalso. apply hnotImp. right. now split.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
  - destruct piBranch.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
    + exact hand.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
  - destruct piBranch.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
    + exact hor.
    + use_without_conditional hwithout.
    + use_without_conditional hwithout.
  - destruct piBranch; use_without_conditional hwithout.
  - destruct piBranch; use_without_conditional hwithout.
Qed.

(** The split is exact, not merely sufficient: a family omitting only the
    implication diagonals projects both the thirty-eight-cell family and the
    two Boolean pairs. *)
Theorem
    raw_dynamicTruthLocalCollisionPairFamilyWithoutConditionalAt_of_without_imp :
    forall (M : RawPAModel) context
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutConditionalAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M context lowerPi lowerSigma hfamily sigmaBranch piBranch hnot.
  apply hfamily.
  intro himp.
  apply hnot. left. exact himp.
Qed.

Theorem
    raw_dynamicTruthLocalBooleanDiagonalPairRootsAt_of_without_imp :
    forall (M : RawPAModel) context
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalBooleanDiagonalPairRootsAt M context.
Proof.
  intros M context lowerPi lowerSigma hfamily. split.
  - apply (hfamily DTLocalSigmaAnd DTLocalPiAnd).
    unfold DynamicTruthImpDiagonalCell.
    intros [[hsigma hpi] | [hsigma hpi]]; discriminate.
  - apply (hfamily DTLocalSigmaOr DTLocalPiOr).
    unfold DynamicTruthImpDiagonalCell.
    intros [[hsigma hpi] | [hsigma hpi]]; discriminate.
Qed.

Theorem raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_iff_split :
    forall (M : RawPAModel) context
      lowerPiApplication lowerSigmaApplication,
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M context
    lowerPiApplication lowerSigmaApplication <->
  RawDynamicTruthLocalCollisionPairFamilyWithoutConditionalAt M context
    lowerPiApplication lowerSigmaApplication /\
  RawDynamicTruthLocalBooleanDiagonalPairRootsAt M context.
Proof.
  intros M context lowerPi lowerSigma. split.
  - intro hfamily. split.
    + exact
        (raw_dynamicTruthLocalCollisionPairFamilyWithoutConditionalAt_of_without_imp
          M context lowerPi lowerSigma hfamily).
    + exact
        (raw_dynamicTruthLocalBooleanDiagonalPairRootsAt_of_without_imp
          M context lowerPi lowerSigma hfamily).
  - intros [hwithout hboolean].
    exact
      (raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_without_conditional_and_boolean
        M context lowerPi lowerSigma hwithout hboolean).
Qed.

(** The predecessor-free part of the trace-linked reduced kernel.  These
    three roots, plus exact-row projection, are sufficient for all
    non-conditional matrix cells. *)
Record RawDynamicTruthNativeLocalNonConditionalReducedKernelInputsAt
    (M : RawPAModel) (context lowerPiApplication lowerSigmaApplication : M)
    : Prop := {
  rawDynamicTruthNativeLocalNonConditionalReducedKernel_sigmaExCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaExPiExCrossLevelPremiseCode M
        lowerSigmaApplication);
  rawDynamicTruthNativeLocalNonConditionalReducedKernel_sigmaAllCrossRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthSigmaAllPiAllCrossLevelPremiseCode M
        lowerPiApplication);
  rawDynamicTruthNativeLocalNonConditionalReducedKernel_mixedReplayRoot :
    RawDynamicTruthLocalRootAt M context
      (rawDynamicTruthMixedQFReplayExclusivityCode M)
}.

Arguments RawDynamicTruthNativeLocalNonConditionalReducedKernelInputsAt
  M context lowerPiApplication lowerSigmaApplication : clear implicits.

(** Exact rows recover adequacy, both direct traces, and all binder
    projections.  Thus a witnessed native invocation needs only the three
    roots in the reduced kernel above. *)
Theorem
    raw_dynamicTruthNativeLocalNonConditionalResidualInputsAt_of_exact_rows_on_witnessed_base :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication
      witnessList baseContext,
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawDynamicTruthNativeLocalNonConditionalReducedKernelInputsAt M
    baseContext lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalNonConditionalResidualInputsAt M
    baseContext lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    witnessList baseContext htrace hlinked hwitness kernel.
  pose proof
    (raw_dynamicTruthNativeLocalProofTraceAt_linked_adequacy
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma htrace hlinked)
    as hadequacy.
  destruct hadequacy as
    [_hsigmaDomain _hpiDomain _hsigmaEvidence _hpiEvidence
      _hadmissible _hsigmaRowDomain _hpiRowDomain hlowerPi hlowerSigma].
  destruct
    (raw_dynamicTruthNativeLocalExactRows_lower_direct_traces_on_witnessed_base
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext htrace hlinked hwitness)
    as [piTrace [sigmaTrace _]].
  refine
    {| rawDynamicTruthNativeLocalNonConditional_lowerPiAdequate :=
         hlowerPi;
       rawDynamicTruthNativeLocalNonConditional_lowerSigmaAdequate :=
         hlowerSigma;
       rawDynamicTruthNativeLocalNonConditional_binderProjections := _;
       rawDynamicTruthNativeLocalNonConditional_sigmaExTrace :=
         inhabits sigmaTrace;
       rawDynamicTruthNativeLocalNonConditional_sigmaAllTrace :=
         inhabits piTrace;
       rawDynamicTruthNativeLocalNonConditional_sigmaExCrossRoot :=
         rawDynamicTruthNativeLocalNonConditionalReducedKernel_sigmaExCrossRoot
           M baseContext lowerPi lowerSigma kernel;
       rawDynamicTruthNativeLocalNonConditional_sigmaAllCrossRoot :=
         rawDynamicTruthNativeLocalNonConditionalReducedKernel_sigmaAllCrossRoot
           M baseContext lowerPi lowerSigma kernel;
       rawDynamicTruthNativeLocalNonConditional_mixedReplayRoot :=
         rawDynamicTruthNativeLocalNonConditionalReducedKernel_mixedReplayRoot
           M baseContext lowerPi lowerSigma kernel |}.
  intro cell.
  exact
    (raw_dynamicTruthNativeLocalExactRows_binder_projections_on_witnessed_base
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext htrace hlinked hwitness cell).
Qed.

(** End-to-end production on the witnessed base from the smaller forty
    helpers.  The only additional hypothesis is the honest two-root Boolean
    residual. *)
Theorem
    raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_40_helpers_and_nonconditional_residual :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList context helperRoots
      lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndAllMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalNonConditionalResidualInputsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalBooleanDiagonalPairRootsAt M context ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList context helperRoots
    lowerPi lowerSigma hagreement hwitness hhelpers residual hboolean.
  apply
    (raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_without_conditional_and_boolean
      M context lowerPi lowerSigma).
  - apply
      (raw_dynamicTruthLocalCollisionPairFamilyWithoutConditionalAt_of_inputs
        M hPA context lowerPi lowerSigma).
    exact
      (raw_dynamicTruthLocalNonConditionalCollisionInputsAt_of_40_helpers
        M hPA translation witnessList context helperRoots
        lowerPi lowerSigma hagreement hwitness hhelpers residual).
  - exact hboolean.
Qed.

(** Guarded-batch wrapper.  It consumes only the forty-helper prefix and
    intentionally discards the two implication cells: those are applied
    later with the guarded implication predecessor. *)
Theorem
    raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_42_helpers_and_nonconditional_residual :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList context helperRoots
      lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawFixedPAHelperBatchLocalProofs M translation context
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalNonConditionalResidualInputsAt M context
    lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalBooleanDiagonalPairRootsAt M context ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M context
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList context helperRoots
    lowerPi lowerSigma hagreement hwitness hhelpers residual hboolean.
  destruct (raw_dynamicTruthNativeLocal_helper_roots_of_42_helpers
    M hPA translation context helperRoots hagreement hhelpers) as
    (legacyRoots & hlegacy & _hfalse & _htrue).
  exact
    (raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_40_helpers_and_nonconditional_residual
      M hPA translation witnessList context legacyRoots
      lowerPi lowerSigma hagreement hwitness hlegacy residual hboolean).
Qed.

(** Trace-linked guarded-batch endpoint for the thirty-eight cells. *)
Theorem
    raw_dynamicTruthLocalCollisionPairFamilyWithoutConditionalAt_of_42_helpers_on_exact_rows :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList baseContext helperRoots
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalNonConditionalReducedKernelInputsAt M
    baseContext lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutConditionalAt M
    baseContext lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    hagreement hwitness hhelpers htrace hlinked kernel.
  pose proof
    (raw_dynamicTruthNativeLocalNonConditionalResidualInputsAt_of_exact_rows_on_witnessed_base
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPi lowerSigma
      witnessList baseContext htrace hlinked hwitness kernel)
    as residual.
  destruct (raw_dynamicTruthNativeLocal_helper_roots_of_42_helpers
    M hPA translation baseContext helperRoots hagreement hhelpers) as
    (legacyRoots & hlegacy & _hfalse & _htrue).
  apply
    (raw_dynamicTruthLocalCollisionPairFamilyWithoutConditionalAt_of_inputs
      M hPA baseContext lowerPi lowerSigma).
  exact
    (raw_dynamicTruthLocalNonConditionalCollisionInputsAt_of_40_helpers
      M hPA translation witnessList baseContext legacyRoots
      lowerPi lowerSigma hagreement hwitness hlegacy residual).
Qed.

(** Trace-linked guarded-batch endpoint for all non-implication cells.  The
    Boolean pair record is the exact remaining source obligation by the
    equivalence above. *)
Theorem
    raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_42_helpers_on_exact_rows_and_boolean :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      translation witnessList baseContext helperRoots
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence
      sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication,
  RawCodedTemplatePAAgreement M translation ->
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawFixedPAHelperBatchLocalProofs M translation baseContext
    rawDynamicTruthReadyAndGuardedMixedQFPAHelpers helperRoots ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthNativeLocalExactRowParametersAt M predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthNativeLocalNonConditionalReducedKernelInputsAt M
    baseContext lowerPiApplication lowerSigmaApplication ->
  RawDynamicTruthLocalBooleanDiagonalPairRootsAt M baseContext ->
  RawDynamicTruthLocalCollisionPairFamilyWithoutImpAt M
    baseContext lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA translation witnessList baseContext helperRoots
    tail predecessorLevel inputGlobalSigma inputGlobalPi
    sigmaDomain piDomain sigmaEvidence piEvidence
    sigmaRowDomain piRowDomain lowerPi lowerSigma
    hagreement hwitness hhelpers htrace hlinked kernel hboolean.
  apply
    (raw_dynamicTruthLocalCollisionPairFamilyWithoutImpAt_of_without_conditional_and_boolean
      M baseContext lowerPi lowerSigma).
  - exact
      (raw_dynamicTruthLocalCollisionPairFamilyWithoutConditionalAt_of_42_helpers_on_exact_rows
        M hPA translation witnessList baseContext helperRoots
        tail predecessorLevel inputGlobalSigma inputGlobalPi
        sigmaDomain piDomain sigmaEvidence piEvidence
        sigmaRowDomain piRowDomain lowerPi lowerSigma
        hagreement hwitness hhelpers htrace hlinked kernel).
  - exact hboolean.
Qed.

End
  PABoundedRawCodedDynamicTruthNativeLocalGuardedNonImpPairCompilation.
