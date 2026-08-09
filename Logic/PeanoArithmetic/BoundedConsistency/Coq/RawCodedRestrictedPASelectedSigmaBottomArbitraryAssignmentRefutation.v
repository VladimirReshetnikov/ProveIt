(**
  Assignment-parametric refutation of native Sigma truth for falsity.

  The older selected-Sigma refutation specializes the global truth source
  at [(bot, 0, 0)].  That endpoint is sufficient for closed consistency,
  but it cannot be composed with a recursive rule case whose assignment
  coordinates are still live.  This module repeats only the binder-sensitive
  opening boundary at

      [(bot, #assignmentCodeIndex, #assignmentStepIndex)].

  The two indices are meta-theoretically arbitrary.  Every time the source
  is opened below its ten global witnesses, the corresponding terms are
  explicitly lifted by ten.  This is the important difference from merely
  replacing the two zero constants in the old closed proof.

  The contradiction itself is assignment-independent.  Once the selected
  successor-Sigma row is opened, its QF branch asks for a positive rank-zero
  certificate for falsity at the displayed assignment, and every other
  branch assigns a non-bottom constructor code to falsity.  Seven ordinary
  open PA theorems refute those principals, after which the existing finite
  disjunction and existential-elimination compilers close the source.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFixedLevelTruthTotality
  RawCodedRankZeroTruthStepFunctionality
  RawCodedFixedLevelBottomLaws
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofTaggedChoice
  RawCodedProofAssumptionLeaf
  RawCodedProofImpIConstructor
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionDerivedCases
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofExistentialEliminationChain
  RawCodedPAAxiomWitnessPrefix
  RawCodedZeroOneDistinctnessProofCompilation
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateParameterAbstraction
  RawCodedTemplateFormulaAtomicAdequacy
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedTruthCertificateMasterFixedHelperBatchExtension
  RawCodedDynamicTruthLocalCollisionMatrixAssembly
  RawCodedDynamicTruthNativeLocalStagedRootCompilation
  RawCodedDynamicTruthNativeLocalStagedCallbackCompilation
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthGlobalOpenedRowSelection
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary
  RawCodedRestrictedPASelectedSigmaBottomGlobalOpenedBranchRefutations
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly
  RawCodedDynamicTruthNativeAlignedRootApplicationIdentification
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPASelectedSigmaBottomArbitraryAssignmentRefutation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedRankZeroTruthStepFunctionality.
Import PABoundedRawCodedFixedLevelBottomLaws.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPALocalProofTaggedChoice.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionDerivedCases.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofExistentialEliminationChain.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedZeroOneDistinctnessProofCompilation.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateFormulaAtomicAdequacy.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedTruthCertificateMasterFixedHelperBatchExtension.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedRootCompilation.
Import PABoundedRawCodedDynamicTruthNativeLocalStagedCallbackCompilation.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthGlobalOpenedRowSelection.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedSevenCaseBoundary.
Import
  PABoundedRawCodedRestrictedPASelectedSigmaBottomGlobalOpenedBranchRefutations.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedFourStateTableAppendPermutedTemplateGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthNativeAlignedRootApplicationIdentification.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthNativeAlignedStrongStepLogicalRootsCompilation.

(** ------------------------------------------------------------------
    The exact mode-zero source at an arbitrary pair of assignment variables. *)

Definition coqRestrictedPASelectedSigmaBottomAssignmentSourceAt
    (assignmentCodeIndex assignmentStepIndex : nat) : TemplateFormula :=
  coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate
    (embedPATerm rawFormulaBotCodeTerm)
    (ttVar assignmentCodeIndex) (ttVar assignmentStepIndex).

Definition coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt
    (assignmentCodeIndex assignmentStepIndex : nat) : TemplateFormula :=
  match templateExistentialBodyMany 10
    (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt
      assignmentCodeIndex assignmentStepIndex) with
  | Some body => body
  | None => tfBot
  end.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentTraversalBody_success :
  forall assignmentCodeIndex assignmentStepIndex,
  templateExistentialBodyMany 10
    (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt
      assignmentCodeIndex assignmentStepIndex) =
  Some (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt
    assignmentCodeIndex assignmentStepIndex).
Proof. intros. reflexivity. Qed.

Definition coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
    (assignmentCodeIndex assignmentStepIndex : nat)
    (sourcePrefix : TemplateContext) : TemplateContext :=
  match templateExistentialEliminationContext 10
    (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt
      assignmentCodeIndex assignmentStepIndex) sourcePrefix with
  | Some context => context
  | None => []
  end.

Lemma
    coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn_success :
  forall assignmentCodeIndex assignmentStepIndex sourcePrefix,
  templateExistentialEliminationContext 10
    (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt
      assignmentCodeIndex assignmentStepIndex) sourcePrefix =
  Some (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
    assignmentCodeIndex assignmentStepIndex sourcePrefix).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn_head :
  forall assignmentCodeIndex assignmentStepIndex sourcePrefix,
  exists tail,
    coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
      assignmentCodeIndex assignmentStepIndex sourcePrefix =
    coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt
      assignmentCodeIndex assignmentStepIndex :: tail.
Proof. intros. eexists. reflexivity. Qed.

(** Total projections are convenient here because the preceding success
    lemma records that the fallback branch is unreachable. *)
Definition coqRestrictedPASelectedSigmaBottomAssignmentModeDefinedAt a s :=
  templateAnd7First
    (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentFormulaDefinedAt a s :=
  templateAnd7Second
    (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s).
Definition
    coqRestrictedPASelectedSigmaBottomAssignmentCodeDefinedAt a s :=
  templateAnd7Third
    (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s).
Definition
    coqRestrictedPASelectedSigmaBottomAssignmentStepDefinedAt a s :=
  templateAnd7Fourth
    (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentRootBoundAt a s :=
  templateAnd7Fifth
    (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentRootLookupAt a s :=
  templateAnd7Sixth
    (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentRowsAt a s :=
  templateAnd7Seventh
    (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s).

Lemma coqRestrictedPASelectedSigmaBottomAssignmentTraversalBody_shape :
  forall a s,
  coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s =
  tfAnd (coqRestrictedPASelectedSigmaBottomAssignmentModeDefinedAt a s)
    (tfAnd
      (coqRestrictedPASelectedSigmaBottomAssignmentFormulaDefinedAt a s)
      (tfAnd
        (coqRestrictedPASelectedSigmaBottomAssignmentCodeDefinedAt a s)
        (tfAnd
          (coqRestrictedPASelectedSigmaBottomAssignmentStepDefinedAt a s)
          (tfAnd
            (coqRestrictedPASelectedSigmaBottomAssignmentRootBoundAt a s)
            (tfAnd
              (coqRestrictedPASelectedSigmaBottomAssignmentRootLookupAt a s)
              (coqRestrictedPASelectedSigmaBottomAssignmentRowsAt a s)))))).
Proof. intros. reflexivity. Qed.

Theorem raw_codedPALocalProofOf_selectedSigmaBottomAssignment_global_fields :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix a s,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofAnd7FieldsAt M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
        a s sourcePrefix))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentModeDefinedAt a s))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentFormulaDefinedAt a s))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentCodeDefinedAt a s))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentStepDefinedAt a s))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentRootBoundAt a s))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentRootLookupAt a s))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentRowsAt a s)).
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix a s
    hwitnessed.
  destruct
    (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn_head
      a s sourcePrefix) as [tail hdeep].
  assert (htail : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation baseContext tail)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitnessed).
  }
  assert (hbody : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
          a s sourcePrefix))
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s))
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseContext
          (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
            a s sourcePrefix))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt
            a s)))).
  {
    rewrite hdeep. cbn [rawTemplateContextCodeOnTail].
    exact (raw_codedPALocalProofOf_assumption M hPA
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt a s))
      htail).
  }
  rewrite coqRestrictedPASelectedSigmaBottomAssignmentTraversalBody_shape
    in hbody.
  rewrite !rawTemplateFormula_and in hbody.
  lazymatch type of hbody with
  | RawCodedPALocalProofOf _ _ _ ?bodyRoot =>
      exact (raw_codedPALocalProofOf_and7E M hPA
        (rawTemplateContextCodeOnTail translation baseContext
          (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
            a s sourcePrefix))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentModeDefinedAt a s))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentFormulaDefinedAt a s))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentCodeDefinedAt a s))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentStepDefinedAt a s))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentRootBoundAt a s))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentRootLookupAt a s))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentRowsAt a s))
        bodyRoot hbody)
  end.
Qed.

(** ------------------------------------------------------------------
    The selected successor-Sigma row and its seven assignment-parametric
    branches. *)

(** These aliases spell the row opening before the proof-producing version
    below.  Keeping the syntactic layer separate makes the branch schemata
    available without creating a dependency from arithmetic validity back
    to the row-selection proof. *)
Definition coqRestrictedPASelectedSigmaBottomAssignmentCoreReplacementsAt
    (a s : nat) : list TemplateTerm :=
  [ ttVar 8;
    embedPATerm (Term.numeral 0);
    embedPATerm rawFormulaBotCodeTerm;
    ttVar (10 + a);
    ttVar (10 + s) ].

Definition coqRestrictedPASelectedSigmaBottomAssignmentCoreRowFormulaAt a s :=
  templateUniversalOpenManyOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentRowsAt a s)
    (coqRestrictedPASelectedSigmaBottomAssignmentCoreReplacementsAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentCoreRowChoiceAt a s :=
  templateImpConsequent (templateImpConsequent
    (coqRestrictedPASelectedSigmaBottomAssignmentCoreRowFormulaAt a s)).
Definition coqRestrictedPASelectedSigmaBottomAssignmentCoreLeftBranchAt a s :=
  templateOrLeftOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentCoreRowChoiceAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentCoreSelectedAt a s :=
  templateAndRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentCoreLeftBranchAt a s).

Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s :=
  coqRestrictedPASelectedSigmaBottomAssignmentCoreSelectedAt a s.

Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt a s :=
  match templateExistentialBodyMany 8
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s) with
  | Some body => body
  | None => tfBot
  end.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBody_success :
  forall a s,
  templateExistentialBodyMany 8
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s) =
  Some (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt a s).
Proof. intros. reflexivity. Qed.

Definition coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
    (a s : nat) (sourcePrefix : TemplateContext) : TemplateContext :=
  match templateExistentialEliminationContext 8
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s)
    (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
      a s sourcePrefix) with
  | Some context => context
  | None => []
  end.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn_success :
  forall a s sourcePrefix,
  templateExistentialEliminationContext 8
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s)
    (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
      a s sourcePrefix) =
  Some (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
    a s sourcePrefix).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn_head :
  forall a s sourcePrefix,
  exists tail,
    coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
      a s sourcePrefix =
    coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt a s :: tail.
Proof. intros. eexists. reflexivity. Qed.

Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaDomainAt a s :=
  templateAndLeftOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7At a s :=
  templateAndRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt a s).

Lemma coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBody_shape :
  forall a s,
  coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt a s =
  tfAnd
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaDomainAt a s)
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7At a s).
Proof. intros. reflexivity. Qed.

Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail1At
    a s :=
  templateOrRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7At a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail2At
    a s :=
  templateOrRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail1At a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail3At
    a s :=
  templateOrRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail2At a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail4At
    a s :=
  templateOrRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail3At a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail5At
    a s :=
  templateOrRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail4At a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail6At
    a s :=
  templateOrRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail5At a s).

Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
    (a s : nat) (branch : DynamicTruthLocalSigmaBranch) : TemplateFormula :=
  match branch with
  | DTLocalSigmaQF => templateOrLeftOrBot
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7At a s)
  | DTLocalSigmaImpFalseLeft => templateOrLeftOrBot
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail1At a s)
  | DTLocalSigmaImpTrueRight => templateOrLeftOrBot
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail2At a s)
  | DTLocalSigmaAnd => templateOrLeftOrBot
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail3At a s)
  | DTLocalSigmaOr => templateOrLeftOrBot
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail4At a s)
  | DTLocalSigmaEx => templateOrLeftOrBot
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail5At a s)
  | DTLocalSigmaAll =>
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOrTail6At a s
  end.

Definition coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchesAt
    (a s : nat) : list TemplateFormula :=
  map (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt a s)
    dynamicTruthLocalSigmaBranchOrder.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7_shape :
  forall a s,
  coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7At a s =
  tfOr
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      a s DTLocalSigmaQF)
    (tfOr
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
        a s DTLocalSigmaImpFalseLeft)
      (tfOr
        (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
          a s DTLocalSigmaImpTrueRight)
        (tfOr
          (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
            a s DTLocalSigmaAnd)
          (tfOr
            (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
              a s DTLocalSigmaOr)
            (tfOr
              (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
                a s DTLocalSigmaEx)
              (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
                a s DTLocalSigmaAll)))))).
Proof. intros. reflexivity. Qed.

Theorem raw_codedPALocalProofOf_selectedSigmaBottomAssignment_opened_or7 :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix a s,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
          a s sourcePrefix))
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7At a s))
      root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix a s
    hwitnessed.
  destruct
    (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn_head
      a s sourcePrefix) as [tail hdeep].
  assert (htail : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation baseContext tail)).
  {
    apply (raw_templateContextOnTail_realizable M hPA).
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitnessed).
  }
  assert (hbody : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
          a s sourcePrefix))
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt a s))
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseContext
          (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
            a s sourcePrefix))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt
            a s)))).
  {
    rewrite hdeep. cbn [rawTemplateContextCodeOnTail].
    exact (raw_codedPALocalProofOf_assumption M hPA
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt a s))
      htail).
  }
  rewrite coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBody_shape,
    rawTemplateFormula_and in hbody.
  lazymatch type of hbody with
  | RawCodedPALocalProofOf _ _ _ ?bodyRoot =>
      pose proof (raw_codedPALocalProofOf_andE2 M hPA
        (rawTemplateContextCodeOnTail translation baseContext
          (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
            a s sourcePrefix))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaDomainAt
            a s))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7At a s))
        bodyRoot hbody) as hor;
      eexists; exact hor
  end.
Qed.

(** ------------------------------------------------------------------
    Seven ordinary PA refutations.  Only the QF formula mentions the two
    assignment variables; its validity theorem is nevertheless uniform in
    their values. *)

Definition coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
    (a s : nat) (branch : DynamicTruthLocalSigmaBranch) : TemplateFormula :=
  match branch with
  | DTLocalSigmaQF =>
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
        a s branch
  | _ => templateAndLeftOrBot
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
        a s branch)
  end.

Definition coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
    (a s : nat) (branch : DynamicTruthLocalSigmaBranch) : TemplateFormula :=
  tfImp
    (coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt a s branch)
    tfBot.

Definition coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
    (a s : nat) (branch : DynamicTruthLocalSigmaBranch) : formula :=
  match templateFormulaAsPAFormula
    (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      a s branch) with
  | Some output => output
  | None => pBot
  end.

Lemma
    coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutation_reifies :
  forall a s branch,
  templateFormulaAsPAFormula
    (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      a s branch) =
  Some
    (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      a s branch).
Proof. intros a s branch. destruct branch; reflexivity. Qed.

Lemma
    coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutation_embeds :
  forall a s branch,
  embedPAFormula
    (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      a s branch) =
  coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
    a s branch.
Proof.
  intros a s branch.
  exact (templateFormulaAsPAFormula_sound _ _
    (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutation_reifies
      a s branch)).
Qed.

Theorem
    coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPA_raw_valid :
  forall a s branch (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e
    (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      a s branch).
Proof.
  intros a s branch M hPA e. destruct branch.
  - cbn [coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7At
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBodyAt
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt
      coqRestrictedPASelectedSigmaBottomAssignmentCoreSelectedAt
      coqRestrictedPASelectedSigmaBottomAssignmentCoreLeftBranchAt
      coqRestrictedPASelectedSigmaBottomAssignmentCoreRowChoiceAt
      coqRestrictedPASelectedSigmaBottomAssignmentCoreRowFormulaAt
      coqRestrictedPASelectedSigmaBottomAssignmentCoreReplacementsAt
      coqRestrictedPASelectedSigmaBottomAssignmentRowsAt
      coqRestrictedPASelectedSigmaBottomAssignmentTraversalBodyAt
      coqRestrictedPASelectedSigmaBottomAssignmentSourceAt
      raw_formula_sat].
    intro hcertificate.
    pose proof (raw_rankZeroTruthCertificate_bot_output_zero M hPA
      (rawNumeralValue M 1) _ _ hcertificate) as honeZero.
    exact (raw_zero_neq_truthOne M hPA (eq_sym honeZero)).
  - cbn [coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_binary M hPA 2
      (raw_term_eval M e (tVar 6))
      (raw_term_eval M e (tVar 4))). exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_binary M hPA 2
      (raw_term_eval M e (tVar 6))
      (raw_term_eval M e (tVar 4))). exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_binary M hPA 3
      (raw_term_eval M e (tVar 6))
      (raw_term_eval M e (tVar 4))). exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_binary M hPA 4
      (raw_term_eval M e (tVar 6))
      (raw_term_eval M e (tVar 4))). exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_unary M hPA 6
      (raw_term_eval M e (tVar 6))). exact hcode.
  - cbn [coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
      coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      raw_formula_sat].
    intro hcode.
    apply (raw_formulaBot_neq_unary M hPA 5
      (raw_term_eval M e (tVar 6))). exact hcode.
Qed.

Theorem
    PA_proves_coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutation :
  forall a s branch,
  Formula.BProv Formula.Ax_s []
    (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
      a s branch).
Proof.
  intros a s branch. apply PA_proves_open_formula_of_raw_valid.
  exact
    (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPA_raw_valid
      a s branch).
Qed.

Definition rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelperAt
    (a s : nat) (branch : DynamicTruthLocalSigmaBranch) : RawFixedPAHelper :=
  {| rawFixedPAHelperFormula :=
       coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
         a s branch;
     rawFixedPAHelperBProv :=
       PA_proves_coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutation
         a s branch |}.

Definition rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelpersAt
    (a s : nat) : list RawFixedPAHelper :=
  map (rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelperAt a s)
    dynamicTruthLocalSigmaBranchOrder.

Lemma rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelper_target :
  forall (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) a s branch,
  rawFixedPAHelperTranslatedTargetCode M translation
    (rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelperAt
      a s branch) =
  rawTemplateFormula translation
    (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
      a s branch).
Proof.
  intros M translation a s branch.
  unfold rawFixedPAHelperTranslatedTargetCode,
    rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelperAt.
  change (rawTemplateFormula translation
    (embedPAFormula
      (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationPAAt
        a s branch)) =
    rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
        a s branch)).
  now rewrite
    coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutation_embeds.
Qed.


(** Beneath the ten global existentials, an outer variable [#i] is [#(10+i)].
    Stating those lifts explicitly prevents capture by the row's five All
    binders. *)
Definition coqRestrictedPASelectedSigmaBottomAssignmentRootRowReplacementsAt
    (a s : nat) : list TemplateTerm :=
  [ ttVar 8;
    embedPATerm (Term.numeral 0);
    embedPATerm rawFormulaBotCodeTerm;
    ttVar (10 + a);
    ttVar (10 + s) ].

Definition coqRestrictedPASelectedSigmaBottomAssignmentRootRowFormulaAt a s :=
  templateUniversalOpenManyOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentRowsAt a s)
    (coqRestrictedPASelectedSigmaBottomAssignmentRootRowReplacementsAt a s).

Definition coqRestrictedPASelectedSigmaBottomAssignmentRootRowChoiceAt a s :=
  templateImpConsequent (templateImpConsequent
    (coqRestrictedPASelectedSigmaBottomAssignmentRootRowFormulaAt a s)).

Definition coqRestrictedPASelectedSigmaBottomAssignmentRootRowLeftBranchAt
    a s :=
  templateOrLeftOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentRootRowChoiceAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightBranchAt
    a s :=
  templateOrRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentRootRowChoiceAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentRootRowLeftTagAt a s :=
  templateAndLeftOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentRootRowLeftBranchAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentRootRowSelectedAt a s :=
  templateAndRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentRootRowLeftBranchAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightTagAt a s :=
  templateAndLeftOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightBranchAt a s).
Definition coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightPayloadAt
    a s :=
  templateAndRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightBranchAt a s).

Lemma coqRestrictedPASelectedSigmaBottomAssignmentRootRowSelected_core :
  forall a s,
  coqRestrictedPASelectedSigmaBottomAssignmentRootRowSelectedAt a s =
  coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s.
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentRootRowFormula_success :
  forall a s,
  templateUniversalOpenMany
    (coqRestrictedPASelectedSigmaBottomAssignmentRowsAt a s)
    (coqRestrictedPASelectedSigmaBottomAssignmentRootRowReplacementsAt a s) =
  Some (coqRestrictedPASelectedSigmaBottomAssignmentRootRowFormulaAt a s).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentRootRowFormula_shape :
  forall a s,
  coqRestrictedPASelectedSigmaBottomAssignmentRootRowFormulaAt a s =
  tfImp (coqRestrictedPASelectedSigmaBottomAssignmentRootBoundAt a s)
    (tfImp
      (coqRestrictedPASelectedSigmaBottomAssignmentRootLookupAt a s)
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowChoiceAt a s)).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentRootRowChoice_shape :
  forall a s,
  coqRestrictedPASelectedSigmaBottomAssignmentRootRowChoiceAt a s =
  tfOr
    (tfAnd
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowLeftTagAt a s)
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowSelectedAt a s))
    (tfAnd
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightTagAt a s)
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightPayloadAt a s)).
Proof. intros. reflexivity. Qed.

Lemma coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightTag_zero :
  forall a s,
  coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightTagAt a s =
  embedPAFormula zeroEqualsOneFormula.
Proof. intros. reflexivity. Qed.

Theorem
    raw_codedPALocalProofOf_selectedSigmaBottomAssignment_root_row_choice :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix a s,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
          a s sourcePrefix))
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAssignmentRootRowChoiceAt a s))
      root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix a s
    hwitnessed.
  pose proof
    (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_global_fields
      M hPA translation witnessList baseContext sourcePrefix a s hwitnessed)
    as hfields.
  destruct hfields as
    [_hmode _hformula _hassignmentCode _hassignmentStep
      [boundRoot hbound] [lookupRoot hlookup] [rowsRoot hrows]].
  exact
    (raw_codedPALocalProofOf_templateUniversalOpenMany_impE2
      M hPA translation
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
          a s sourcePrefix))
      (coqRestrictedPASelectedSigmaBottomAssignmentRowsAt a s)
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowReplacementsAt
        a s)
      (coqRestrictedPASelectedSigmaBottomAssignmentRootBoundAt a s)
      (coqRestrictedPASelectedSigmaBottomAssignmentRootLookupAt a s)
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowChoiceAt a s)
      rowsRoot boundRoot lookupRoot
      (eq_trans
        (coqRestrictedPASelectedSigmaBottomAssignmentRootRowFormula_success
          a s)
        (f_equal (@Some TemplateFormula)
          (coqRestrictedPASelectedSigmaBottomAssignmentRootRowFormula_shape
            a s)))
      hrows hbound hlookup).
Qed.

Theorem
    raw_codedPALocalProofOf_selectedSigmaBottomAssignment_root_row_selected :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnessList baseContext sourcePrefix a s,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  exists witnesses selectedRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
          a s sourcePrefix))
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAssignmentRootRowSelectedAt a s))
      selectedRoot.
Proof.
  intros M hPA translation hagreement witnessList baseContext sourcePrefix
    a s hwitnessed.
  destruct
    (raw_codedZeroOneDistinctness_roots_on_witnessed_extension
      M hPA translation hagreement witnessList baseContext hwitnessed)
    as (witnesses & zeroNotOneRoot & _oneNotZeroRoot &
      hextended & hincluded & hzeroNotOne & _honeNotZero).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).
  set (deepPrefix :=
    coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
      a s sourcePrefix).
  assert (hextendedRealizable : RawContextListRealizable M extendedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      extendedContext hextended).
  }
  assert (hdeepPrefixAdequate :
      RawCodedTemplatePrefixAtomicallyAdequate M translation deepPrefix).
  {
    intros input _.
    exact (raw_codedTemplateFormula_atomically_adequate_core
      M hPA translation input).
  }
  destruct (raw_codedPALocalProof_templatePrefix M hPA translation
    extendedContext deepPrefix _ zeroNotOneRoot hextendedRealizable
    hdeepPrefixAdequate hzeroNotOne)
    as [deepZeroNotOneRoot hdeepZeroNotOne].
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_root_row_choice
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses witnessList)
      extendedContext sourcePrefix a s hextended)
    as [choiceRoot hchoice].
  assert (hdeepRealizable : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)).
  {
    exact (raw_templateContextOnTail_realizable M hPA translation
      extendedContext deepPrefix hextendedRealizable).
  }
  assert (hchoiceZero := hchoice).
  rewrite coqRestrictedPASelectedSigmaBottomAssignmentRootRowChoice_shape,
    rawTemplateFormula_or, !rawTemplateFormula_and in hchoiceZero.
  assert (hnotRight : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightTagAt
            a s))
        (rawFormulaBotCode M)) deepZeroNotOneRoot).
  {
    change (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
      (rawTemplateFormula translation
        (tfImp (embedPAFormula zeroEqualsOneFormula) tfBot))
      deepZeroNotOneRoot) in hdeepZeroNotOne.
    rewrite rawTemplateFormula_imp, rawTemplateFormula_bot
      in hdeepZeroNotOne.
    rewrite
      coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightTag_zero.
    exact hdeepZeroNotOne.
  }
  assert (hrightAdequate : RawCodedFormulaAtomicallyAdequate M
      (rawFormulaAndCode M
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightTagAt
            a s))
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightPayloadAt
            a s)))).
  {
    rewrite <- rawTemplateFormula_and.
    exact (raw_codedTemplateFormula_atomically_adequate_core
      M hPA translation
      (tfAnd
        (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightTagAt a s)
        (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightPayloadAt
          a s))).
  }
  destruct (raw_codedPALocalProofOf_taggedChoice_left M hPA
    (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowLeftTagAt a s))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowSelectedAt a s))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightTagAt a s))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentRootRowRightPayloadAt
        a s))
    choiceRoot deepZeroNotOneRoot hdeepRealizable hrightAdequate
    hchoiceZero hnotRight) as [selectedRoot hselected].
  exists witnesses, selectedRoot.
  split; [exact hextended |].
  split; [exact hincluded | exact hselected].
Qed.

(** ------------------------------------------------------------------
    From principal refutations to the seven full branch refutations. *)

Definition coqRestrictedPASelectedSigmaBottomAssignmentBranchRemainderAt
    (a s : nat) (branch : DynamicTruthLocalSigmaBranch) : TemplateFormula :=
  templateAndRightOrBot
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      a s branch).

Lemma coqRestrictedPASelectedSigmaBottomAssignmentBranch_shape_non_qf :
  forall a s branch,
  branch <> DTLocalSigmaQF ->
  coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      a s branch =
  tfAnd
    (coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
      a s branch)
    (coqRestrictedPASelectedSigmaBottomAssignmentBranchRemainderAt
      a s branch).
Proof.
  intros a s branch hnot. destruct branch; try reflexivity.
  exfalso. apply hnot. reflexivity.
Qed.

Theorem
    raw_codedPALocalProofOf_selectedSigmaBottomAssignment_branch_refutation_of_principal :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context a s branch principalRoot,
  RawContextListRealizable M context ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
        a s branch)) principalRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
            a s branch))
        (rawFormulaBotCode M)) root.
Proof.
  intros M hPA translation context a s branch principalRoot
    hcontext hprincipal.
  set (branchFormula :=
    coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
      a s branch).
  set (principal :=
    coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
      a s branch).
  unfold coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
    in hprincipal.
  fold principal in hprincipal.
  rewrite rawTemplateFormula_imp, rawTemplateFormula_bot in hprincipal.
  assert (hbranchAdequate : RawCodedFormulaAtomicallyAdequate M
      (rawTemplateFormula translation branchFormula)).
  {
    apply raw_codedTemplateFormula_atomically_adequate_core.
    exact hPA.
  }
  destruct
    (raw_codedPALocalProof_adequateConsTransplant M hPA context
      (rawTemplateFormula translation branchFormula)
      (rawFormulaImpCode M
        (rawTemplateFormula translation principal)
        (rawFormulaBotCode M))
      principalRoot hbranchAdequate hcontext hprincipal)
    as [liftedPrincipalRoot hliftedPrincipal].
  pose proof (raw_codedPALocalProofOf_assumption M hPA context
    (rawTemplateFormula translation branchFormula) hcontext)
    as hbranchAssumption.
  subst branchFormula. subst principal.
  assert (hprincipalAssumption : exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
              a s branch)) context)
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
            a s branch)) root).
  {
    Ltac project_assignment_non_qf
        constructorName model pa trans ctx aa ss branchHyp :=
      let hshape := fresh "hshape" in
      assert (hshape :=
        coqRestrictedPASelectedSigmaBottomAssignmentBranch_shape_non_qf
          aa ss constructorName ltac:(discriminate));
      rewrite hshape, rawTemplateFormula_and in branchHyp;
      try rewrite hshape, rawTemplateFormula_and;
      eexists;
      exact (raw_codedPALocalProofOf_andE1 model pa
        (rawListNode model
          (rawFormulaAndCode model
            (rawTemplateFormula trans
              (coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
                aa ss constructorName))
            (rawTemplateFormula trans
              (coqRestrictedPASelectedSigmaBottomAssignmentBranchRemainderAt
                aa ss constructorName))) ctx)
        (rawTemplateFormula trans
          (coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
            aa ss constructorName))
        (rawTemplateFormula trans
          (coqRestrictedPASelectedSigmaBottomAssignmentBranchRemainderAt
            aa ss constructorName))
        _ branchHyp).
    destruct branch.
    - exists (rawProofAssumptionRoot M
        (rawListNode M
          (rawTemplateFormula translation
            (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
              a s DTLocalSigmaQF)) context)
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
            a s DTLocalSigmaQF))).
      unfold
        coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt.
      exact hbranchAssumption.
    - project_assignment_non_qf constr:(DTLocalSigmaImpFalseLeft)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        constr:(a) constr:(s) hbranchAssumption.
    - project_assignment_non_qf constr:(DTLocalSigmaImpTrueRight)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        constr:(a) constr:(s) hbranchAssumption.
    - project_assignment_non_qf constr:(DTLocalSigmaAnd)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        constr:(a) constr:(s) hbranchAssumption.
    - project_assignment_non_qf constr:(DTLocalSigmaOr)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        constr:(a) constr:(s) hbranchAssumption.
    - project_assignment_non_qf constr:(DTLocalSigmaEx)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        constr:(a) constr:(s) hbranchAssumption.
    - project_assignment_non_qf constr:(DTLocalSigmaAll)
        constr:(M) constr:(hPA) constr:(translation) constr:(context)
        constr:(a) constr:(s) hbranchAssumption.
  }
  destruct hprincipalAssumption as [projectedRoot hprojected].
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawListNode M
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
          a s branch)) context)
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentBranchPrincipalAt
        a s branch))
    (rawFormulaBotCode M)
    liftedPrincipalRoot projectedRoot hliftedPrincipal hprojected) as hbottom.
  lazymatch type of hbottom with
  | RawCodedPALocalProofOf _ _ _ ?bottomRoot =>
      exists (rawProofImpIRoot M context
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
            a s branch))
        (rawFormulaBotCode M) bottomRoot);
      exact (raw_codedPALocalProofOf_impI M hPA context
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
            a s branch))
        (rawFormulaBotCode M) bottomRoot hbottom)
  end.
Qed.

Definition rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (a s : nat) : list M :=
  map
    (fun branch => rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
        a s branch))
    dynamicTruthLocalSigmaBranchOrder.

Arguments rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
  M translation a s : clear implicits.

Lemma rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranches_disjunction :
  forall (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) a s,
  rawFiniteRightDisjunctionCode M
    (rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
      M translation a s) =
  rawTemplateFormula translation
    (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7At a s).
Proof.
  intros M translation a s.
  unfold rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt,
    dynamicTruthLocalSigmaBranchOrder.
  cbn [map rawFiniteRightDisjunctionCode].
  rewrite coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaOr7_shape,
    !rawTemplateFormula_or.
  reflexivity.
Qed.

Record RawRestrictedPASelectedSigmaBottomAssignmentSevenCaseSupportAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseContext : M) (sourcePrefix : TemplateContext)
    (a s : nat) : Prop := {
  rawRestrictedPASelectedSigmaBottomAssignment_caseResources :
    RawFiniteDisjunctionDerivedCaseResources M
      (rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
        M translation a s)
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
          a s sourcePrefix));
  rawRestrictedPASelectedSigmaBottomAssignment_branchRoots :
    forall branch : DynamicTruthLocalSigmaBranch,
      exists root,
        RawCodedPALocalProofOf M
          (rawTemplateContextCodeOnTail translation baseContext
            (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
              a s sourcePrefix))
          (rawFormulaImpCode M
            (rawTemplateFormula translation
              (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
                a s branch))
            (rawFormulaBotCode M)) root
}.

Arguments RawRestrictedPASelectedSigmaBottomAssignmentSevenCaseSupportAt
  M translation baseContext sourcePrefix a s : clear implicits.

Theorem
    raw_restrictedPASelectedSigmaBottomAssignmentSevenCaseSupport_growing :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    baseWitnessList baseContext sourcePrefix a s,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawRestrictedPASelectedSigmaBottomAssignmentSevenCaseSupportAt
      M translation
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      sourcePrefix a s.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext sourcePrefix a s hbase.
  destruct
    (raw_fixedPAHelperBatch_on_witnessed_tail
      M hPA translation hagreement
      (rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelpersAt a s)
      baseWitnessList baseContext hbase)
    as (prefix & helperRoots & hextended & hhelpers).
  set (extendedWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      prefix baseWitnessList).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext).
  assert (hincluded : RawContextListIncluded M baseContext extendedContext).
  {
    unfold extendedContext.
    exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
      M hPA prefix baseContext).
  }
  assert (hextendedRealizable : RawContextListRealizable M extendedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      extendedWitnessList extendedContext hextended).
  }
  set (deepPrefix :=
    coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
      a s sourcePrefix).
  assert (hdeepRealizable : RawContextListRealizable M
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)).
  {
    exact (raw_templateContextOnTail_realizable M hPA translation
      extendedContext deepPrefix hextendedRealizable).
  }
  assert (hdeepAdequate :
      RawCodedTemplatePrefixAtomicallyAdequate M translation deepPrefix).
  {
    intros formula _hin.
    exact (raw_codedTemplateFormula_atomically_adequate_core
      M hPA translation formula).
  }
  exists prefix. split; [exact hextended |].
  split; [exact hincluded |].
  constructor.
  - apply (raw_finiteDisjunctionDerivedCaseResources_of_members_here
      M hPA
      (rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
        M translation a s)
      (rawTemplateContextCodeOnTail translation extendedContext deepPrefix));
      [exact hdeepRealizable |].
    intros encodedBranch hencodedBranch.
    unfold rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
      in hencodedBranch.
    apply in_map_iff in hencodedBranch.
    destruct hencodedBranch as [branch [<- _]].
    exact (raw_codedTemplateFormula_atomically_adequate_core
      M hPA translation
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaBranchAt
        a s branch)).
  - intro branch.
    assert (hhelperIn : In
        (rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelperAt
          a s branch)
        (rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelpersAt
          a s)).
    {
      unfold
        rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelpersAt.
      apply in_map.
      exact (dynamicTruthLocalSigmaBranchOrder_complete_here branch).
    }
    destruct
      (raw_fixedPAHelperBatchLocalProofs_member
        M translation extendedContext
        (rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelpersAt a s)
        helperRoots
        (rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelperAt
          a s branch)
        hhelpers hhelperIn)
      as [principalRoot hprincipal].
    rewrite
      rawRestrictedPASelectedSigmaBottomAssignmentRefutationHelper_target
      in hprincipal.
    destruct
      (raw_codedPALocalProof_templatePrefix M hPA translation
        extendedContext deepPrefix
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentPrincipalRefutationAt
            a s branch))
        principalRoot hextendedRealizable hdeepAdequate hprincipal)
      as [deepPrincipalRoot hdeepPrincipal].
    exact
      (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_branch_refutation_of_principal
        M hPA translation
        (rawTemplateContextCodeOnTail translation extendedContext deepPrefix)
        a s branch deepPrincipalRoot hdeepRealizable hdeepPrincipal).
Qed.

(** ------------------------------------------------------------------
    Close Or7, then Ex8, then the genuine AtRootTerms Ex10 source. *)

Theorem raw_codedPALocalProofOf_selectedSigmaBottomAssignment_local_bottom :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix a s,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawRestrictedPASelectedSigmaBottomAssignmentSevenCaseSupportAt
    M translation baseContext sourcePrefix a s ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
          a s sourcePrefix))
      (rawFormulaBotCode M) root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix a s
    hwitnessed hsupport.
  destruct hsupport as [hresources hbranchRoots].
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_opened_or7
      M hPA translation witnessList baseContext sourcePrefix a s hwitnessed)
    as [orRoot hor].
  assert (hrow : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
          a s sourcePrefix))
      (rawFiniteRightDisjunctionCode M
        (rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
          M translation a s)) orRoot).
  {
    rewrite
      rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranches_disjunction.
    exact hor.
  }
  assert (hcases : RawCodedPALocalFiniteDisjunctionCaseFamily M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
          a s sourcePrefix))
      (rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
        M translation a s)
      (rawFormulaBotCode M)).
  {
    intros selected hselected.
    unfold rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
      in hselected.
    apply in_map_iff in hselected.
    destruct hselected as [branch [hselected _]]. subst selected.
    exact (hbranchRoots branch).
  }
  exact
    (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
      M hPA
      (rawRestrictedPASelectedSigmaBottomAssignmentOpenedBranchesAt
        M translation a s)
      (rawFormulaBotCode M)
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
          a s sourcePrefix))
      orRoot hresources hrow hcases).
Qed.

Theorem
    raw_codedPALocalProofOf_selectedSigmaBottomAssignment_global_deep_bottom :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext sourcePrefix a s selectedRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
        a s sourcePrefix))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s))
    selectedRoot ->
  RawRestrictedPASelectedSigmaBottomAssignmentSevenCaseSupportAt
    M translation baseContext sourcePrefix a s ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
          a s sourcePrefix))
      (rawFormulaBotCode M) root.
Proof.
  intros M hPA translation witnessList baseContext sourcePrefix a s
    selectedRoot hwitnessed hselected hsupport.
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_local_bottom
      M hPA translation witnessList baseContext sourcePrefix a s
      hwitnessed hsupport) as [deepRoot hdeep].
  assert (hdeepTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
          a s sourcePrefix))
      (rawTemplateFormula translation
        (templateFormulaShiftMany 8 tfBot)) deepRoot).
  {
    cbn [templateFormulaShiftMany templateFormulaRename].
    rewrite rawTemplateFormula_bot. exact hdeep.
  }
  destruct
    (raw_codedPALocalProofOf_existential_elimination_chain_on_witnessed_tail
      M hPA translation witnessList baseContext 8
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s)
      (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
        a s sourcePrefix)
      tfBot
      (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn
        a s sourcePrefix)
      selectedRoot deepRoot hwitnessed
      (coqRestrictedPASelectedSigmaBottomAssignmentLocalDeepContextOn_success
        a s sourcePrefix)
      hselected hdeepTemplate) as [root hroot].
  exists root. rewrite rawTemplateFormula_bot in hroot. exact hroot.
Qed.

Theorem raw_codedPALocalProofOf_selectedSigmaBottomAssignment_refutation :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext a s selectedRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
        a s
        [coqRestrictedPASelectedSigmaBottomAssignmentSourceAt a s]))
    (rawTemplateFormula translation
      (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s))
    selectedRoot ->
  RawRestrictedPASelectedSigmaBottomAssignmentSevenCaseSupportAt
    M translation baseContext
      [coqRestrictedPASelectedSigmaBottomAssignmentSourceAt a s] a s ->
  exists root,
    RawCodedPALocalProofOf M baseContext
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt a s))
        (rawFormulaBotCode M)) root.
Proof.
  intros M hPA translation witnessList baseContext a s selectedRoot
    hwitnessed hselected hsupport.
  set (source :=
    coqRestrictedPASelectedSigmaBottomAssignmentSourceAt a s).
  set (sourcePrefix := ([source] : TemplateContext)).
  assert (hbaseRealizable : RawContextListRealizable M baseContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitnessed).
  }
  assert (hsource : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext sourcePrefix)
      (rawTemplateFormula translation source)
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseContext sourcePrefix)
        (rawTemplateFormula translation source))).
  {
    unfold sourcePrefix. cbn [rawTemplateContextCodeOnTail].
    exact (raw_codedPALocalProofOf_assumption M hPA baseContext
      (rawTemplateFormula translation source) hbaseRealizable).
  }
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_global_deep_bottom
      M hPA translation witnessList baseContext sourcePrefix a s selectedRoot
      hwitnessed hselected hsupport) as [deepRoot hdeep].
  assert (hdeepTemplate : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext
        (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
          a s sourcePrefix))
      (rawTemplateFormula translation
        (templateFormulaShiftMany 10 tfBot)) deepRoot).
  {
    cbn [templateFormulaShiftMany templateFormulaRename].
    rewrite rawTemplateFormula_bot. exact hdeep.
  }
  destruct
    (raw_codedPALocalProofOf_existential_elimination_chain_on_witnessed_tail
      M hPA translation witnessList baseContext 10 source sourcePrefix
      tfBot
      (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
        a s sourcePrefix)
      (rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseContext sourcePrefix)
        (rawTemplateFormula translation source))
      deepRoot hwitnessed
      (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn_success
        a s sourcePrefix)
      hsource hdeepTemplate) as [bottomRoot hbottom].
  exists (rawProofImpIRoot M baseContext
    (rawTemplateFormula translation source) (rawFormulaBotCode M)
    bottomRoot).
  rewrite rawTemplateFormula_bot in hbottom.
  unfold sourcePrefix in hbottom.
  cbn [rawTemplateContextCodeOnTail] in hbottom.
  exact (raw_codedPALocalProofOf_impI M hPA baseContext
    (rawTemplateFormula translation source) (rawFormulaBotCode M)
    bottomRoot hbottom).
Qed.

(** Main endpoint: both the mode-selection witnesses and all seven fixed PA
    helpers are synchronized into one finite standard witness prefix. *)
Theorem
    raw_codedPALocalProofOf_selectedSigmaBottomAssignment_refutation_compiled_growing :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    baseWitnessList baseContext a s,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt a s))
        (rawFormulaBotCode M)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext a s hbase.
  set (source :=
    coqRestrictedPASelectedSigmaBottomAssignmentSourceAt a s).
  set (sourcePrefix := ([source] : TemplateContext)).
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_root_row_selected
      M hPA translation hagreement baseWitnessList baseContext
      sourcePrefix a s hbase)
    as (rowPrefix & selectedRoot & hrowWitnessed & hrowIncluded & hselected).
  rewrite
    coqRestrictedPASelectedSigmaBottomAssignmentRootRowSelected_core
    in hselected.
  set (rowWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      rowPrefix baseWitnessList).
  set (rowContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M rowPrefix baseContext).
  destruct
    (raw_restrictedPASelectedSigmaBottomAssignmentSevenCaseSupport_growing
      M hPA translation hagreement rowWitnessList rowContext
      sourcePrefix a s hrowWitnessed)
    as (casePrefix & hcaseWitnessed & hrowCaseIncluded & hsupport).
  set (finalWitnessList :=
    rawStandardPAAxiomWitnessPrefixWitnessListCode M
      casePrefix rowWitnessList).
  set (finalContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M casePrefix rowContext).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      rowWitnessList rowContext finalWitnessList finalContext
      (coqRestrictedPASelectedSigmaBottomAssignmentGlobalDeepContextOn
        a s sourcePrefix)
      (rawTemplateFormula translation
        (coqRestrictedPASelectedSigmaBottomAssignmentOpenedSigmaRowAt a s))
      selectedRoot hrowWitnessed hcaseWitnessed hrowCaseIncluded hselected)
    as [transportedSelectedRoot htransportedSelected].
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_refutation
      M hPA translation finalWitnessList finalContext a s
      transportedSelectedRoot hcaseWitnessed htransportedSelected hsupport)
    as [root hroot].
  exists (casePrefix ++ rowPrefix), root.
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app,
    rawStandardPAAxiomWitnessPrefixContextCode_app.
  split; [exact hcaseWitnessed |].
  split.
  - intros member hmember. apply hrowCaseIncluded. apply hrowIncluded.
    exact hmember.
  - unfold source in hroot. exact hroot.
Qed.

(** Literal-template presentation of the same endpoint.  Most downstream
    recursive-rule modules state their goals through [rawTemplateFormula],
    so exposing [tfImp source tfBot] here avoids asking each consumer to
    repeat the two translation rewrites. *)
Corollary
    raw_codedPALocalProofOf_selectedSigmaBottomAssignment_template_refutation_compiled_growing :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    baseWitnessList baseContext a s,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawTemplateFormula translation
        (tfImp
          (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt a s)
          tfBot)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext a s hbase.
  destruct
    (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_refutation_compiled_growing
      M hPA translation hagreement baseWitnessList baseContext a s hbase)
    as (prefix & root & hwitnessed & hincluded & hroot).
  exists prefix, root. split; [exact hwitnessed |].
  split; [exact hincluded |].
  rewrite rawTemplateFormula_imp, rawTemplateFormula_bot.
  exact hroot.
Qed.

(** The recursive Bottom-E case uses precisely variables nine and eight.
    This corollary is intentionally just a specialization of the arbitrary
    assignment compiler; no normalization to the empty assignment occurs. *)
Corollary
    raw_codedPALocalProofOf_selectedSigmaBottomCurrentAssignment_refutation_compiled_growing :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8))
        (rawFormulaBotCode M)) root.
Proof.
  intros. eapply
    raw_codedPALocalProofOf_selectedSigmaBottomAssignment_refutation_compiled_growing;
    eauto.
Qed.

(** Template-shaped specialization used by the recursive Bottom-E branch.
    Its antecedent still names the live assignment pair [(#9,#8)]. *)
Corollary
    raw_codedPALocalProofOf_selectedSigmaBottomCurrentAssignment_template_refutation_compiled_growing :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation -> forall
    baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists (prefix : StandardPAAxiomWitnessPrefix) root,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawTemplateFormula translation
        (tfImp
          (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8)
          tfBot)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext hbase.
  exact
    (raw_codedPALocalProofOf_selectedSigmaBottomAssignment_template_refutation_compiled_growing
      M hPA translation hagreement baseWitnessList baseContext 9 8 hbase).
Qed.

Lemma coqRestrictedPASelectedSigmaBottomCurrentAssignmentSource_shape :
  coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8 =
  coqFourStateTableAppendTemplateGlobalSourceAtRootTerms 0
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate
    (embedPATerm rawFormulaBotCodeTerm) (ttVar 9) (ttVar 8).
Proof. reflexivity. Qed.

(** The antecedent selected above is definitionally the same opaque truth
    leaf used by [coqRestrictedPADirectBottomCurrentTruthTemplate]; the
    latter is intentionally not imported here, so this compiler can remain
    below the recursive Bottom-E module in the dependency graph. *)
Lemma coqRestrictedPASelectedSigmaBottomCurrentAssignmentAlignedTruth_shape :
  coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
    (embedPATerm rawFormulaBotCodeTerm) (ttVar 9) (ttVar 8) =
  tfOpaque coqRestrictedPAConclusionTruthPredicateName
    [coqRestrictedPASoundnessLowerLevelTerm;
     coqRestrictedPASoundnessUpperLevelTerm;
     embedPATerm rawFormulaBotCodeTerm; ttVar 9; ttVar 8].
Proof. reflexivity. Qed.

(** Aligned native structural inputs identify the preceding exact source
    with the direct conclusion-truth selector at the same root tuple. *)
Theorem raw_selectedSigmaBottomCurrentAssignmentSource_aligned_reroot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (tail : nat -> M) predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi
    (aligned : RawDynamicTruthNativeLocalAlignedPredecessorAt M tail
      predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi)
    inputLevelNumeral
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthNativeAlignedStrongStepStructuralInputsAt
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned
      inputLevelNumeral inputs ->
  rawDirectTemplateFormula inputs
    (coqRestrictedPASelectedSigmaBottomAssignmentSourceAt 9 8) =
  rawDirectTemplateFormula inputs
    (coqDynamicTruthNativeAlignedSigmaEvidenceAtRootTerms
      (embedPATerm rawFormulaBotCodeTerm) (ttVar 9) (ttVar 8)).
Proof.
  intros M hPA tail predecessorLevel baseContext currentLocal
    nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
    inputs hstructural.
  exact (proj1
    (raw_dynamicTruthNativeAligned_global_evidence_reroot
      M hPA tail predecessorLevel baseContext currentLocal
      nextInputGlobalSigma nextInputGlobalPi aligned inputLevelNumeral
      inputs hstructural)
    (embedPATerm rawFormulaBotCodeTerm) (ttVar 9) (ttVar 8)).
Qed.

End
  PABoundedRawCodedRestrictedPASelectedSigmaBottomArbitraryAssignmentRefutation.
