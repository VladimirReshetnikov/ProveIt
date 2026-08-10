(**
  Growing-tail compilation of the three same-context unary recursive cases.

  And-E-left, And-E-right, and Or-I-right all recurse into one child whose
  displayed context is the parent context.  The pointwise represented
  compiler is already shared by
  [RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation],
  but the post-And-I continuation still asks for the three resulting laws on
  one common standard-PA witness tail.  This module supplies the missing
  affine layer.

  The generic first section applies to any affine ready-context constructor:
  an arithmetic child-interface compiler is transformed into the recursive
  truth law without adding witnesses.  The branch section then synchronizes
  three independently growing interface compilers.  Finally, an eleven-field
  continuation record deletes precisely these three recursive coordinates
  from the historical fourteen-field post-And-I record and reconstructs that
  record after the synchronized arithmetic interfaces have been compiled.

  Thus the remaining branch-specific boundary contains no opaque truth
  target: each new premise asks only for the represented arithmetic bundle
  inherited by the recursive child.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedPALocalProofExistential
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateLocalProofAffineStandardWitnessTailTransport
  RawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity
  RawCodedRestrictedPADerivationSoundnessDirectAssumptionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase
  RawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase
  RawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase
  RawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase
  RawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase
  RawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation
  RawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import
  PABoundedRawCodedTemplateLocalProofAffineStandardWitnessTailTransport.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStandardReadyContextAffinity.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAssumptionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationLeftCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndEliminationRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionRightCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectUniversalEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialIntroductionCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExistentialEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityReflexivityCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectEqualityEliminationCase.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildCompilation.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleCasesAfterAndIntroduction.

(** ------------------------------------------------------------------
    Constructor-independent standard-tail compiler. *)

Definition
    RawCoqRestrictedPASameContextUnaryChildInterfaceStandardTailCompilerAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (contextAt : TemplateContext -> TemplateContext)
    (child witnessContext childConclusion : TemplateTerm) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPASameContextUnaryChildInterfaceRootAt M
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (contextAt (embedPAContext (map witnessedAxiom witnesses)))
        child witnessContext childConclusion).

Definition
    RawCoqRestrictedPASameContextUnaryRecursiveChildLawRootAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (contextAt : TemplateContext -> TemplateContext)
    (child witnessContext childConclusion : TemplateTerm)
    (displayedEndpoint : TemplateFormula)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  exists lawRoot : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (contextAt (embedPAContext (map witnessedAxiom witnesses))))
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfImp displayedEndpoint
          (tfImp
            (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
              child witnessContext childConclusion)
            (coqRestrictedPADirectAndIntroductionChildTruthTemplate
              child witnessContext childConclusion))))
      lawRoot.

Definition
    RawCoqRestrictedPASameContextUnaryRecursiveChildLawStandardTailCompilerAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (contextAt : TemplateContext -> TemplateContext)
    (child witnessContext childConclusion : TemplateTerm)
    (displayedEndpoint : TemplateFormula) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPASameContextUnaryRecursiveChildLawRootAtWitnesses
      M hPA inputs contextAt child witnessContext childConclusion
      displayedEndpoint).

Arguments
  RawCoqRestrictedPASameContextUnaryChildInterfaceStandardTailCompilerAt
  M hPA inputs contextAt child witnessContext childConclusion
  : clear implicits.
Arguments
  RawCoqRestrictedPASameContextUnaryRecursiveChildLawRootAtWitnesses
  M hPA inputs contextAt child witnessContext childConclusion
  displayedEndpoint witnesses : clear implicits.
Arguments
  RawCoqRestrictedPASameContextUnaryRecursiveChildLawStandardTailCompilerAt
  M hPA inputs contextAt child witnessContext childConclusion
  displayedEndpoint : clear implicits.

(** The conversion is pointwise in the selected witness batch: the K-proof
    and strong-prefix application are finite template proofs, so they require
    no additional standard PA axioms. *)
Theorem
    raw_sameContextUnary_recursiveChildLawStandardTailCompiler_of_interface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (contextAt : TemplateContext -> TemplateContext)
    child witnessContext childConclusion displayedEndpoint,
  (forall tail,
    In coqRestrictedPADirectAndIntroductionDeepStrongPrefixTemplate
      (contextAt tail)) ->
  RawCoqRestrictedPASameContextUnaryChildInterfaceStandardTailCompilerAt
    M hPA inputs contextAt child witnessContext childConclusion ->
  RawCoqRestrictedPASameContextUnaryRecursiveChildLawStandardTailCompilerAt
    M hPA inputs contextAt child witnessContext childConclusion
    displayedEndpoint.
Proof.
  intros M hPA inputs contextAt child witnessContext childConclusion
    displayedEndpoint hprefix hinterface baseWitnesses.
  destruct (hinterface baseWitnesses) as [suffix hinterfaceAt].
  exists suffix.
  exact
    (raw_sameContextUnary_recursiveChildLawRootAt_of_interface
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (contextAt
        (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix))))
      child witnessContext childConclusion displayedEndpoint
      (hprefix
        (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix))))
      hinterfaceAt).
Qed.

(** The same abstraction gives append stability for every compiled law.  It
    is stated separately because synchronization of independently selected
    branch suffixes needs to transport the earlier laws. *)
Theorem
    raw_sameContextUnary_recursiveChildLawRootAtWitnesses_append_stable :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (contextAt : TemplateContext -> TemplateContext)
    child witnessContext childConclusion displayedEndpoint,
  (forall witnesses,
    contextAt (embedPAContext (map witnessedAxiom witnesses)) =
      contextAt [] ++ embedPAContext (map witnessedAxiom witnesses)) ->
  RawCoqStandardWitnessTailAppendStable
    (RawCoqRestrictedPASameContextUnaryRecursiveChildLawRootAtWitnesses
      M hPA inputs contextAt child witnessContext childConclusion
      displayedEndpoint).
Proof.
  intros M hPA inputs contextAt child witnessContext childConclusion
    displayedEndpoint haffine.
  unfold
    RawCoqRestrictedPASameContextUnaryRecursiveChildLawRootAtWitnesses.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      contextAt haffine
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (tfImp displayedEndpoint
          (tfImp
            (coqRestrictedPADirectAndIntroductionChildContextTruthTemplate
              child witnessContext childConclusion)
            (coqRestrictedPADirectAndIntroductionChildTruthTemplate
              child witnessContext childConclusion))))).
Qed.

(** ------------------------------------------------------------------
    Exact branch contexts and arithmetic interface compilers. *)

Lemma
    coqRestrictedPADirectSameContextUnary_andEliminationLeft_readyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  change
    (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectAndEliminationLeftCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
     coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectAndEliminationLeftCaseTemplate [] ++
     embedPAContext (map witnessedAxiom witnesses)).
  apply coqRestrictedPADirectStandardReadyContext_app_witnesses.
Qed.

Lemma
    coqRestrictedPADirectSameContextUnary_andEliminationRight_readyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepAndEliminationRightReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepAndEliminationRightReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  change
    (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectAndEliminationRightCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
     coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectAndEliminationRightCaseTemplate [] ++
     embedPAContext (map witnessedAxiom witnesses)).
  apply coqRestrictedPADirectStandardReadyContext_app_witnesses.
Qed.

Lemma
    coqRestrictedPADirectSameContextUnary_orIntroductionRight_readyContext_app_witnesses :
    forall witnesses,
  coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext
      (embedPAContext (map witnessedAxiom witnesses)) =
  coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext [] ++
    embedPAContext (map witnessedAxiom witnesses).
Proof.
  intro witnesses.
  change
    (coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectOrIntroductionRightCaseTemplate
      (embedPAContext (map witnessedAxiom witnesses)) =
     coqRestrictedPADirectStandardReadyContext
      coqRestrictedPADirectAssumptionOuterContextTruthTemplate
      coqRestrictedPADirectAssumptionDeepAdmissibleTemplate
      coqRestrictedPADirectOrIntroductionRightCaseTemplate [] ++
     embedPAContext (map witnessedAxiom witnesses)).
  apply coqRestrictedPADirectStandardReadyContext_app_witnesses.
Qed.

Definition
    RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceRoot
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).

Definition
    RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectAndEliminationRightChildInterfaceRoot
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).

Definition
    RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceRoot
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).

Arguments
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
  M hPA inputs : clear implicits.
Arguments
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
  M hPA inputs : clear implicits.

(** Bundle the three exact recursive roots at a common witness batch. *)
Definition RawCoqRestrictedPADirectSameContextUnaryRecursiveRootsAtWitnesses
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (witnesses : StandardPAAxiomWitnessPrefix) : Prop :=
  RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) /\
  RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)) /\
  RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
    M hPA inputs (embedPAContext (map witnessedAxiom witnesses)).

Definition
    RawCoqRestrictedPADirectSameContextUnaryRecursiveStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (RawCoqRestrictedPADirectSameContextUnaryRecursiveRootsAtWitnesses
      M hPA inputs).

Arguments RawCoqRestrictedPADirectSameContextUnaryRecursiveRootsAtWitnesses
  M hPA inputs witnesses : clear implicits.
Arguments
  RawCoqRestrictedPADirectSameContextUnaryRecursiveStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem
    raw_andEliminationLeft_recursiveChildStandardTailCompiler_of_interface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).
Proof.
  intros M hPA inputs hinterface baseWitnesses.
  destruct (hinterface baseWitnesses) as [suffix hinterfaceAt].
  exists suffix.
  exact
    (raw_andEliminationLeft_recursiveChildLawRoot_of_sameContextInterface
      M hPA inputs
      (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix)))
      hinterfaceAt).
Qed.

Theorem
    raw_andEliminationRight_recursiveChildStandardTailCompiler_of_interface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).
Proof.
  intros M hPA inputs hinterface baseWitnesses.
  destruct (hinterface baseWitnesses) as [suffix hinterfaceAt].
  exists suffix.
  exact
    (raw_andEliminationRight_recursiveChildLawRoot_of_sameContextInterface
      M hPA inputs
      (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix)))
      hinterfaceAt).
Qed.

Theorem
    raw_orIntroductionRight_recursiveChildStandardTailCompiler_of_interface :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).
Proof.
  intros M hPA inputs hinterface baseWitnesses.
  destruct (hinterface baseWitnesses) as [suffix hinterfaceAt].
  exists suffix.
  exact
    (raw_orIntroductionRight_recursiveChildLawRoot_of_sameContextInterface
      M hPA inputs
      (embedPAContext (map witnessedAxiom (baseWitnesses ++ suffix)))
      hinterfaceAt).
Qed.

(** Each exact branch law is append-stable because its ready context is an
    instance of the common affine spine. *)
Lemma raw_andEliminationLeft_recursiveChildRoot_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (fun witnesses =>
      RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectStrongStepAndEliminationLeftReadyContext
      coqRestrictedPADirectSameContextUnary_andEliminationLeft_readyContext_app_witnesses
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAndEliminationLeftRecursiveChildLawTemplate)).
Qed.

Lemma raw_andEliminationRight_recursiveChildRoot_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (fun witnesses =>
      RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectStrongStepAndEliminationRightReadyContext
      coqRestrictedPADirectSameContextUnary_andEliminationRight_readyContext_app_witnesses
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectAndEliminationRightRecursiveChildLawTemplate)).
Qed.

Lemma raw_orIntroductionRight_recursiveChildRoot_append_stable : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqStandardWitnessTailAppendStable
    (fun witnesses =>
      RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).
Proof.
  intros M hPA inputs.
  unfold
    RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot.
  exact
    (raw_codedPALocalProof_affine_context_root_append_stable
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      coqRestrictedPADirectStrongStepOrIntroductionRightReadyContext
      coqRestrictedPADirectSameContextUnary_orIntroductionRight_readyContext_app_witnesses
      (rawDirectTemplateFormula inputs
        coqRestrictedPADirectOrIntroductionRightRecursiveChildLawTemplate)).
Qed.

(** The three arithmetic interface compilers may choose unrelated finite
    suffixes.  Two uses of the generic affine conjunction combinator select a
    single suffix while transporting the earlier represented roots. *)
Theorem raw_sameContextUnaryRecursiveStandardTailCompiler_of_interfaces :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectSameContextUnaryRecursiveStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hleft hright hor.
  pose proof
    (raw_andEliminationLeft_recursiveChildStandardTailCompiler_of_interface
      M hPA inputs hleft) as hleftLaw.
  pose proof
    (raw_andEliminationRight_recursiveChildStandardTailCompiler_of_interface
      M hPA inputs hright) as hrightLaw.
  pose proof
    (raw_orIntroductionRight_recursiveChildStandardTailCompiler_of_interface
      M hPA inputs hor) as horLaw.
  pose proof
    (raw_coqStandardWitnessTailCompiler_and _ _
      (raw_andEliminationRight_recursiveChildRoot_append_stable
        M hPA inputs)
      hrightLaw horLaw) as hrightAndOr.
  pose proof
    (raw_coqStandardWitnessTailCompiler_and _ _
      (raw_andEliminationLeft_recursiveChildRoot_append_stable
        M hPA inputs)
      hleftLaw hrightAndOr) as hall.
  exact hall.
Qed.

(** ------------------------------------------------------------------
    The exact eleven-coordinate continuation after deleting the three
    same-context recursive fields. *)

Record
    RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionExceptSameContextUnaryRecursive
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (tail : TemplateContext) : Prop := {
  rawCoqRestrictedPADirectAfterAndIExceptUnary_andEliminationLeftTruth :
    RawCoqRestrictedPADirectAndEliminationLeftDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_andEliminationRightTruth :
    RawCoqRestrictedPADirectAndEliminationRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_orIntroductionRightTruth :
    RawCoqRestrictedPADirectOrIntroductionRightDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_orElimination :
    RawCoqRestrictedPADirectOrEliminationSemanticRoots M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_universalIntroduction :
    RawCoqRestrictedPADirectUniversalIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_universalEliminationRecursive :
    RawCoqRestrictedPADirectUniversalEliminationRecursiveChildLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_universalEliminationTruth :
    RawCoqRestrictedPADirectUniversalEliminationDynamicTruthLawRoot
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_existentialIntroduction :
    RawCoqRestrictedPADirectStrongStepExistentialIntroductionSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_existentialElimination :
    RawCoqRestrictedPADirectExistentialEliminationSemanticRoots
      M hPA inputs tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_equalityReflexivity :
    RawCoqRestrictedPADirectEqualityReflexivityAtomicTruthLawRoot M
      (rawDirectStructuralTemplateTranslation M hPA inputs) tail;
  rawCoqRestrictedPADirectAfterAndIExceptUnary_equalityElimination :
    RawCoqRestrictedPADirectStrongStepEqualityEliminationSemanticRoots
      M hPA inputs tail
}.

Arguments
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionExceptSameContextUnaryRecursive
  M hPA inputs tail : clear implicits.

Definition
    RawCoqRestrictedPADirectRemainingAfterAndIntroductionExceptSameContextUnaryRecursiveStandardTailCompiler
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop :=
  RawCoqStandardWitnessTailCompiler
    (fun witnesses =>
      RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionExceptSameContextUnaryRecursive
        M hPA inputs
        (embedPAContext (map witnessedAxiom witnesses))).

Arguments
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionExceptSameContextUnaryRecursiveStandardTailCompiler
  M hPA inputs : clear implicits.

Theorem raw_afterAndIntroduction_of_sameContextUnaryRecursive_and_remainder :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  RawCoqRestrictedPADirectAndEliminationLeftRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectAndEliminationRightRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectOrIntroductionRightRecursiveChildLawRoot
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroductionExceptSameContextUnaryRecursive
    M hPA inputs tail ->
  RawCoqRestrictedPADirectRuleCaseSemanticRootsAfterAndIntroduction
    M hPA inputs tail.
Proof.
  intros M hPA inputs tail hleft hright hor hremaining.
  destruct hremaining.
  constructor; assumption.
Qed.

(** Public continuation reduction.  The only three newly exposed residuals
    are arithmetic child-interface compilers; all opaque truth laws and all
    other genuine recursive/eigenvariable branches stay in the smaller
    eleven-coordinate continuation. *)
Theorem
    raw_remainingAfterAndIntroductionCompiler_of_sameContextUnaryInterfaces :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqRestrictedPADirectAndEliminationLeftChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectAndEliminationRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectOrIntroductionRightChildInterfaceStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionExceptSameContextUnaryRecursiveStandardTailCompiler
    M hPA inputs ->
  RawCoqRestrictedPADirectRemainingAfterAndIntroductionStandardTailCompiler
    M hPA inputs.
Proof.
  intros M hPA inputs hleft hright hor hremaining baseWitnesses.
  pose proof
    (raw_sameContextUnaryRecursiveStandardTailCompiler_of_interfaces
      M hPA inputs hleft hright hor) as hrecursive.
  destruct (hrecursive baseWitnesses) as
    [recursiveSuffix [hleftLaw [hrightLaw horLaw]]].
  destruct (hremaining (baseWitnesses ++ recursiveSuffix)) as
    [remainingSuffix hremainingAt].
  exists (recursiveSuffix ++ remainingSuffix).
  replace (baseWitnesses ++ (recursiveSuffix ++ remainingSuffix)) with
      ((baseWitnesses ++ recursiveSuffix) ++ remainingSuffix)
    by (symmetry; apply app_assoc).
  apply raw_afterAndIntroduction_of_sameContextUnaryRecursive_and_remainder.
  - exact
      (raw_andEliminationLeft_recursiveChildRoot_append_stable
        M hPA inputs (baseWitnesses ++ recursiveSuffix) remainingSuffix
        hleftLaw).
  - exact
      (raw_andEliminationRight_recursiveChildRoot_append_stable
        M hPA inputs (baseWitnesses ++ recursiveSuffix) remainingSuffix
        hrightLaw).
  - exact
      (raw_orIntroductionRight_recursiveChildRoot_append_stable
        M hPA inputs (baseWitnesses ++ recursiveSuffix) remainingSuffix
        horLaw).
  - exact hremainingAt.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessSameContextUnaryRecursiveChildStandardTailCompilation.
