(**
  Proof-code compilation of the native binder principal projections.

  The preceding binder-off-diagonal module isolates two local implications
  per collision cell: each literal Ex8 branch must imply the Ex8 formula
  retaining only its principal-constructor assertion.  This file compiles
  those implications by the transparent repeated-existential projection
  template.  Pure logical templates contain no PA-axiom leaves, so compiling
  them over a witnessed PA context preserves that context literally.

  Fixed branches are discharged without any lower-application premise.  For
  Sigma-All and Pi-Ex, the same proof template is translated with the native
  ternary-application direct inputs.  The only nontransparent resource is
  therefore the already established direct-input identification (or,
  equivalently, the selector shift/opening commutation used to construct it).
  No semantic truth statement is converted into an object proof.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFixedLevelTruth
  RawCodedFixedLevelTruthTotality
  RawCodedNumeralTermCode
  RawCodedFormulaShiftTreeRealization
  RawCodedTemplateSyntax
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedRestrictedPAProof
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateNumeralParameters
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthUniversalLeafProofCompilation
  RawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph
  RawCodedDynamicTruthConstructorBranchDisjointness
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedPALocalProofExistential
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTernaryPredicateDeepClosure
  RawCodedTernaryPredicateDeepClosureShiftInterchange
  RawCodedTernaryPredicateDeepClosureOpeningInterchange
  RawCodedTernaryPredicateDeepClosureOpeningCommuting
  RawCodedDynamicTruthBinderOffDiagonalExclusivity.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthBinderPrincipalProjectionCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFixedLevelTruth.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthRestrictedUniversalLocalProofFieldGraph.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTernaryPredicateDeepClosureShiftInterchange.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningInterchange.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningCommuting.
Import PABoundedRawCodedDynamicTruthBinderOffDiagonalExclusivity.
Import PABoundedRawCodedDynamicTruthConstructorBranchDisjointness.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedPALocalProofExistential.

(** ------------------------------------------------------------------
    One transparent proof template, used by every branch. *)

Definition binderPrincipalProjectionTemplateFormula
    (principal remainder : TemplateFormula) : TemplateFormula :=
  tfImp
    (templateRepeatedExists 8 (tfAnd principal remainder))
    (templateRepeatedExists 8 principal).

Definition binderPrincipalProjectionTemplateProof
    (principal remainder : TemplateFormula) : TemplateRawProof :=
  templateRepeatedExistsSelectionProof 8
    [principal] remainder [] 0.

Lemma binderPrincipalProjectionTemplateProof_derives : forall
    principal remainder,
  TemplateRawDerives []
    (binderPrincipalProjectionTemplateFormula principal remainder)
    (binderPrincipalProjectionTemplateProof principal remainder).
Proof.
  intros principal remainder.
  unfold binderPrincipalProjectionTemplateFormula,
    binderPrincipalProjectionTemplateProof.
  pose proof (templateRepeatedExistsSelectionProof_derives
    8 [principal] remainder [] 0) as hprojection.
  cbn [templateRightConjunction templateSelectedRightConjunction
    templateRightConjunctionSelect map] in hprojection.
  exact hprojection.
Qed.

Definition rawBinderPrincipalProjectionTemplateRoot
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (context : M) (principal remainder : TemplateFormula) : M :=
  rawTemplateProofCodeOnTail translation context
    (binderPrincipalProjectionTemplateProof principal remainder).

Arguments rawBinderPrincipalProjectionTemplateRoot
  M translation context principal remainder : clear implicits.

(** The empty template context folds to [context] exactly. *)
Theorem raw_codedPALocalProofOf_binderPrincipalProjectionTemplate : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (translation : RawCodedTemplateTranslation M)
      witnessList context principal remainder,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (binderPrincipalProjectionTemplateFormula principal remainder))
    (rawBinderPrincipalProjectionTemplateRoot M translation context
      principal remainder).
Proof.
  intros M hPA translation witnessList context principal remainder hcontext.
  pose proof (raw_templateProofOnPAAxiomContext_localProof M hPA
    translation witnessList context
    (binderPrincipalProjectionTemplateProof principal remainder)
    hcontext
    (proj1 (binderPrincipalProjectionTemplateProof_derives
      principal remainder))) as hcompiled.
  cbn [templateRawContext rawTemplateContextCodeOnTail] in hcompiled.
  exact hcompiled.
Qed.

(** ------------------------------------------------------------------
    The fixed branches are ordinary structural templates. *)

Definition formulaAndRightOrBottom (input : formula) : formula :=
  match input with
  | pAnd _ remainder => remainder
  | _ => pBot
  end.

Definition dynamicTruthSigmaFixedPrincipalRemainder
    (branch : DynamicTruthSigmaConstructorBranch) : formula :=
  formulaAndRightOrBottom
    (dynamicTruthSigmaConstructorBranchBody branch pBot).

Definition dynamicTruthPiFixedPrincipalRemainder
    (branch : DynamicTruthPiConstructorBranch) : formula :=
  formulaAndRightOrBottom
    (dynamicTruthPiConstructorBranchBody branch pBot).

Lemma dynamicTruthSigmaFixedPrincipal_split : forall branch,
  dynamicTruthSigmaConstructorBranchBody branch pBot =
  pAnd (dynamicTruthSigmaPrincipalBody branch)
    (dynamicTruthSigmaFixedPrincipalRemainder branch).
Proof. intros []; reflexivity. Qed.

Lemma dynamicTruthPiFixedPrincipal_split : forall branch,
  dynamicTruthPiConstructorBranchBody branch pBot =
  pAnd (dynamicTruthPiPrincipalBody branch)
    (dynamicTruthPiFixedPrincipalRemainder branch).
Proof. intros []; reflexivity. Qed.

Definition dynamicTruthSigmaFixedPrincipalProjectionTemplateFormula
    (branch : DynamicTruthSigmaConstructorBranch) : TemplateFormula :=
  binderPrincipalProjectionTemplateFormula
    (embedPAFormula (dynamicTruthSigmaPrincipalBody branch))
    (embedPAFormula (dynamicTruthSigmaFixedPrincipalRemainder branch)).

Definition dynamicTruthSigmaFixedPrincipalProjectionTemplateProof
    (branch : DynamicTruthSigmaConstructorBranch) : TemplateRawProof :=
  binderPrincipalProjectionTemplateProof
    (embedPAFormula (dynamicTruthSigmaPrincipalBody branch))
    (embedPAFormula (dynamicTruthSigmaFixedPrincipalRemainder branch)).

Definition dynamicTruthPiFixedPrincipalProjectionTemplateFormula
    (branch : DynamicTruthPiConstructorBranch) : TemplateFormula :=
  binderPrincipalProjectionTemplateFormula
    (embedPAFormula (dynamicTruthPiPrincipalBody branch))
    (embedPAFormula (dynamicTruthPiFixedPrincipalRemainder branch)).

Definition dynamicTruthPiFixedPrincipalProjectionTemplateProof
    (branch : DynamicTruthPiConstructorBranch) : TemplateRawProof :=
  binderPrincipalProjectionTemplateProof
    (embedPAFormula (dynamicTruthPiPrincipalBody branch))
    (embedPAFormula (dynamicTruthPiFixedPrincipalRemainder branch)).

(** A bottom fallback is sufficient because the fixed templates contain no
    opaque atoms.  It merely completes the total translation record. *)
Definition rawBinderProjectionZeroNumeralParameters
    (M : RawPAModel) (zeroTermCode : M)
    (hzero : RawNumeralTermCodeAt M (raw_zero M) zeroTermCode)
    : RawCodedTemplateNumeralParameters M :=
  {| rawNumeralTemplateParameterBound := fun _ => raw_zero M;
     rawNumeralTemplateParameterCode := fun _ => zeroTermCode;
     rawNumeralTemplateParameter_valid := fun _ => hzero |}.

Definition rawBinderProjectionBottomStructuralInputs
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    : RawCodedTemplateStructuralInputs M.
Proof.
  pose (opaqueCode :=
    fun (_ : TemplatePredicateName) (_ : list M) => rawFormulaBotCode M).
  refine
    {| rawStructuralTemplateSymbols :=
         rawNumeralTemplateSymbols M parameters opaqueCode;
       rawStructuralTemplateTermShiftAt := _;
       rawStructuralTemplateTermOpeningAt := _;
       rawStructuralTemplateOpaqueShiftTree :=
         fun depth _ _ => RFSTBot M (rawNumeralValue M depth);
       rawStructuralTemplateOpaqueShiftTree_depth := _;
       rawStructuralTemplateOpaqueShiftTree_source := _;
       rawStructuralTemplateOpaqueShiftTree_target := _;
       rawStructuralTemplateOpaqueShiftTree_valid := _;
       rawStructuralTemplateOpaqueOpenTree :=
         fun depth _ _ _ => RFSTBot M (rawNumeralValue M depth);
       rawStructuralTemplateOpaqueOpenTree_depth := _;
       rawStructuralTemplateOpaqueOpenTree_source := _;
       rawStructuralTemplateOpaqueOpenTree_target := _;
       rawStructuralTemplateOpaqueOpenTree_valid := _ |}.
  - exact (raw_numeralTemplateTerm_shift M hPA parameters opaqueCode).
  - exact (raw_numeralTemplateTerm_substitutionAtom
      M hPA parameters opaqueCode).
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. exact I.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. exact I.
Defined.

Lemma rawStructural_sigmaFixedPrincipalProjection_identified : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M) branch lowerPi,
  branch <> DTSigmaAll ->
  rawStructuralTemplateFormula inputs
    (dynamicTruthSigmaFixedPrincipalProjectionTemplateFormula branch) =
  rawFormulaImpCode M
    (rawDynamicTruthSigmaCarrierConstructorEx8BranchCode
      M branch lowerPi)
    (rawFixedFormulaNumeralCode M
      (dynamicTruthSigmaPrincipalEx8Formula branch)).
Proof.
  intros M hPA branchInputs branch lowerPi hfixed.
  destruct branch; try (exfalso; apply hfixed; reflexivity);
    unfold dynamicTruthSigmaFixedPrincipalProjectionTemplateFormula,
      binderPrincipalProjectionTemplateFormula,
      dynamicTruthSigmaFixedPrincipalRemainder,
      formulaAndRightOrBottom,
      dynamicTruthSigmaPrincipalEx8Formula,
      dynamicTruthSigmaPrincipalBody,
      rawDynamicTruthSigmaCarrierConstructorEx8BranchCode,
      rawDynamicTruthSigmaConstructorEx8BranchCode;
    cbn [templateRepeatedExists rawStructuralTemplateFormula
      rawStructuralTemplateFormulaWith].
  all: try rewrite !rawStructuralTemplateFormula_embedPA.
  all: rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  all: reflexivity.
Qed.

Lemma rawStructural_piFixedPrincipalProjection_identified : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateStructuralInputs M) branch lowerSigma,
  branch <> DTPiEx ->
  rawStructuralTemplateFormula inputs
    (dynamicTruthPiFixedPrincipalProjectionTemplateFormula branch) =
  rawFormulaImpCode M
    (rawDynamicTruthPiCarrierConstructorEx8BranchCode
      M branch lowerSigma)
    (rawFixedFormulaNumeralCode M
      (dynamicTruthPiPrincipalEx8Formula branch)).
Proof.
  intros M hPA branchInputs branch lowerSigma hfixed.
  destruct branch; try (exfalso; apply hfixed; reflexivity);
    unfold dynamicTruthPiFixedPrincipalProjectionTemplateFormula,
      binderPrincipalProjectionTemplateFormula,
      dynamicTruthPiFixedPrincipalRemainder,
      formulaAndRightOrBottom,
      dynamicTruthPiPrincipalEx8Formula,
      dynamicTruthPiPrincipalBody,
      rawDynamicTruthPiCarrierConstructorEx8BranchCode,
      rawDynamicTruthPiConstructorEx8BranchCode;
    cbn [templateRepeatedExists rawStructuralTemplateFormula
      rawStructuralTemplateFormulaWith].
  all: try rewrite !rawStructuralTemplateFormula_embedPA.
  all: rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  all: reflexivity.
Qed.

Theorem raw_codedPALocalProofOf_sigmaFixedPrincipalProjection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context branch lowerPi,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  branch <> DTSigmaAll ->
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthSigmaCarrierConstructorEx8BranchCode
          M branch lowerPi)
        (rawFixedFormulaNumeralCode M
          (dynamicTruthSigmaPrincipalEx8Formula branch))) root.
Proof.
  intros M hPA witnessList context branch lowerPi hcontext hfixed.
  destruct (raw_numeralTermCodeExists_zero M hPA)
    as [zeroTermCode hzero].
  set (parameters := rawBinderProjectionZeroNumeralParameters
    M zeroTermCode hzero).
  set (inputs := rawBinderProjectionBottomStructuralInputs
    M hPA parameters).
  set (translation := rawStructuralTemplateTranslation M hPA inputs).
  exists (rawBinderPrincipalProjectionTemplateRoot M translation context
    (embedPAFormula (dynamicTruthSigmaPrincipalBody branch))
    (embedPAFormula (dynamicTruthSigmaFixedPrincipalRemainder branch))).
  rewrite <- (rawStructural_sigmaFixedPrincipalProjection_identified
    M hPA inputs branch lowerPi hfixed).
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (dynamicTruthSigmaFixedPrincipalProjectionTemplateFormula branch))
    (rawBinderPrincipalProjectionTemplateRoot M translation context
      (embedPAFormula (dynamicTruthSigmaPrincipalBody branch))
      (embedPAFormula (dynamicTruthSigmaFixedPrincipalRemainder branch)))).
  exact (raw_codedPALocalProofOf_binderPrincipalProjectionTemplate
    M hPA translation witnessList context
    (embedPAFormula (dynamicTruthSigmaPrincipalBody branch))
    (embedPAFormula (dynamicTruthSigmaFixedPrincipalRemainder branch))
    hcontext).
Qed.

Theorem raw_codedPALocalProofOf_piFixedPrincipalProjection : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context branch lowerSigma,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  branch <> DTPiEx ->
  exists root : M,
    RawCodedPALocalProofOf M context
      (rawFormulaImpCode M
        (rawDynamicTruthPiCarrierConstructorEx8BranchCode
          M branch lowerSigma)
        (rawFixedFormulaNumeralCode M
          (dynamicTruthPiPrincipalEx8Formula branch))) root.
Proof.
  intros M hPA witnessList context branch lowerSigma hcontext hfixed.
  destruct (raw_numeralTermCodeExists_zero M hPA)
    as [zeroTermCode hzero].
  set (parameters := rawBinderProjectionZeroNumeralParameters
    M zeroTermCode hzero).
  set (inputs := rawBinderProjectionBottomStructuralInputs
    M hPA parameters).
  set (translation := rawStructuralTemplateTranslation M hPA inputs).
  exists (rawBinderPrincipalProjectionTemplateRoot M translation context
    (embedPAFormula (dynamicTruthPiPrincipalBody branch))
    (embedPAFormula (dynamicTruthPiFixedPrincipalRemainder branch))).
  rewrite <- (rawStructural_piFixedPrincipalProjection_identified
    M hPA inputs branch lowerSigma hfixed).
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (dynamicTruthPiFixedPrincipalProjectionTemplateFormula branch))
    (rawBinderPrincipalProjectionTemplateRoot M translation context
      (embedPAFormula (dynamicTruthPiPrincipalBody branch))
      (embedPAFormula (dynamicTruthPiFixedPrincipalRemainder branch)))).
  exact (raw_codedPALocalProofOf_binderPrincipalProjectionTemplate
    M hPA translation witnessList context
    (embedPAFormula (dynamicTruthPiPrincipalBody branch))
    (embedPAFormula (dynamicTruthPiFixedPrincipalRemainder branch))
    hcontext).
Qed.

(** ------------------------------------------------------------------
    Native lower-dependent branches.

    The principal conjuncts of the two binder leaves are still fixed PA
    syntax.  Only the counterexample conjunct contains an opaque ternary
    lower application.  Consequently the projection itself needs just the
    designated opaque-output equality, not either row-domain equality. *)

Definition dynamicTruthSigmaAllPrincipalProjectionTemplateFormula
    : TemplateFormula :=
  binderPrincipalProjectionTemplateFormula
    coqDynamicTruthSigmaUniversalPrefixTemplate
    coqDynamicTruthSigmaNoBinderCounterexampleTemplate.

Definition dynamicTruthPiExPrincipalProjectionTemplateFormula
    : TemplateFormula :=
  binderPrincipalProjectionTemplateFormula
    coqDynamicTruthPiExistentialPrefixTemplate
    coqDynamicTruthPiNoBinderCounterexampleTemplate.

Lemma rawBinderProjectionDirectTemplateFormula_embedPA : forall
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    input,
  rawDirectTemplateFormula inputs (embedPAFormula input) =
  rawQuotedFormulaCode M input.
Proof.
  intros M inputs input.
  unfold rawDirectTemplateFormula.
  apply rawStructuralTemplateFormulaWith_embedPA.
Qed.

Definition rawSigmaAllPrincipalProjectionRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) (context : M) : M :=
  rawBinderPrincipalProjectionTemplateRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) context
    coqDynamicTruthSigmaUniversalPrefixTemplate
    coqDynamicTruthSigmaNoBinderCounterexampleTemplate.

Definition rawPiExPrincipalProjectionRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) (context : M) : M :=
  rawBinderPrincipalProjectionTemplateRoot M
    (rawDirectStructuralTemplateTranslation M hPA inputs) context
    coqDynamicTruthPiExistentialPrefixTemplate
    coqDynamicTruthPiNoBinderCounterexampleTemplate.

Arguments rawSigmaAllPrincipalProjectionRoot M hPA inputs context
  : clear implicits.
Arguments rawPiExPrincipalProjectionRoot M hPA inputs context
  : clear implicits.

Lemma rawDirect_sigmaAllPrincipalProjection_identified : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      lowerPiApplication,
  rawCoqDynamicTruthLowerPiDirectAtomTemplateCode M inputs =
    lowerPiApplication ->
  rawDirectTemplateFormula inputs
    dynamicTruthSigmaAllPrincipalProjectionTemplateFormula =
  rawFormulaImpCode M
    (rawDynamicTruthSigmaCarrierConstructorEx8BranchCode
      M DTSigmaAll lowerPiApplication)
    (rawFixedFormulaNumeralCode M
      (dynamicTruthSigmaPrincipalEx8Formula DTSigmaAll)).
Proof.
  intros M hPA inputs lowerPiApplication hlower.
  unfold dynamicTruthSigmaAllPrincipalProjectionTemplateFormula,
    binderPrincipalProjectionTemplateFormula.
  change (rawFormulaImpCode M
    (rawFormulaEx8Code M
      (rawDirectTemplateFormula inputs
        coqDynamicTruthSigmaUniversalLeafTemplate))
    (rawFormulaEx8Code M
      (rawDirectTemplateFormula inputs
        coqDynamicTruthSigmaUniversalPrefixTemplate)) =
    rawFormulaImpCode M
      (rawDynamicTruthSigmaCarrierConstructorEx8BranchCode
        M DTSigmaAll lowerPiApplication)
      (rawFixedFormulaNumeralCode M
        (dynamicTruthSigmaPrincipalEx8Formula DTSigmaAll))).
  rewrite rawDirect_coqDynamicTruthSigmaUniversalLeafTemplate.
  rewrite hlower.
  unfold rawDynamicTruthSigmaCarrierConstructorEx8BranchCode,
    rawDynamicTruthSigmaUniversalCode,
    rawDynamicTruthSigmaNoBinderCode,
    rawCoqDynamicTruthSigmaUniversalLeafTemplateCode,
    coqDynamicTruthSigmaUniversalPrefixTemplate,
    dynamicTruthSigmaPrincipalEx8Formula,
    dynamicTruthSigmaPrincipalBody,
    fixedLevelEx8.
  try rewrite rawBinderProjectionDirectTemplateFormula_embedPA.
  rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDirect_piExPrincipalProjection_identified : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      lowerSigmaApplication,
  rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode M inputs =
    lowerSigmaApplication ->
  rawDirectTemplateFormula inputs
    dynamicTruthPiExPrincipalProjectionTemplateFormula =
  rawFormulaImpCode M
    (rawDynamicTruthPiCarrierConstructorEx8BranchCode
      M DTPiEx lowerSigmaApplication)
    (rawFixedFormulaNumeralCode M
      (dynamicTruthPiPrincipalEx8Formula DTPiEx)).
Proof.
  intros M hPA inputs lowerSigmaApplication hlower.
  unfold dynamicTruthPiExPrincipalProjectionTemplateFormula,
    binderPrincipalProjectionTemplateFormula.
  change (rawFormulaImpCode M
    (rawDynamicTruthPiFormulaEx8Code M
      (rawDirectTemplateFormula inputs
        coqDynamicTruthPiExistentialLeafTemplate))
    (rawDynamicTruthPiFormulaEx8Code M
      (rawDirectTemplateFormula inputs
        coqDynamicTruthPiExistentialPrefixTemplate)) =
    rawFormulaImpCode M
      (rawDynamicTruthPiCarrierConstructorEx8BranchCode
        M DTPiEx lowerSigmaApplication)
      (rawFixedFormulaNumeralCode M
        (dynamicTruthPiPrincipalEx8Formula DTPiEx))).
  rewrite rawDirect_coqDynamicTruthPiExistentialLeafTemplate.
  rewrite hlower.
  rewrite (rawFixedFormulaNumeralCode_eq_quoted M hPA
    (dynamicTruthPiPrincipalEx8Formula DTPiEx)).
  unfold rawDynamicTruthPiCarrierConstructorEx8BranchCode,
    rawDynamicTruthPiExistentialCode,
    rawDynamicTruthPiNoBinderCode,
    rawCoqDynamicTruthPiExistentialLeafTemplateCode,
    coqDynamicTruthPiExistentialPrefixTemplate.
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA
    dynamicTruthPiRowExistentialPrefixFormula).
  rewrite rawBinderProjectionDirectTemplateFormula_embedPA.
  unfold
    dynamicTruthPiPrincipalEx8Formula,
    dynamicTruthPiPrincipalBody,
    fixedLevelEx8.
  rewrite (rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted M hPA
    dynamicTruthPiRowBinderPrependFormula).
  reflexivity.
Qed.

Theorem raw_codedPALocalProofOf_sigmaAllPrincipalProjection : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      witnessList context
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      lowerPiApplication,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  rawCoqDynamicTruthLowerPiDirectAtomTemplateCode M inputs =
    lowerPiApplication ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaCarrierConstructorEx8BranchCode
        M DTSigmaAll lowerPiApplication)
      (rawFixedFormulaNumeralCode M
        (dynamicTruthSigmaPrincipalEx8Formula DTSigmaAll)))
    (rawSigmaAllPrincipalProjectionRoot M hPA inputs context).
Proof.
  intros M hPA witnessList context inputs lowerPiApplication
    hcontext hlower.
  rewrite <- (rawDirect_sigmaAllPrincipalProjection_identified
    M hPA inputs lowerPiApplication hlower).
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      dynamicTruthSigmaAllPrincipalProjectionTemplateFormula)
    (rawSigmaAllPrincipalProjectionRoot M hPA inputs context)).
  exact (raw_codedPALocalProofOf_binderPrincipalProjectionTemplate
    M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList context
    coqDynamicTruthSigmaUniversalPrefixTemplate
    coqDynamicTruthSigmaNoBinderCounterexampleTemplate hcontext).
Qed.

Theorem raw_codedPALocalProofOf_piExPrincipalProjection : forall
    (M : RawPAModel) (hPA : RawPASatisfies M), forall
      witnessList context
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      lowerSigmaApplication,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode M inputs =
    lowerSigmaApplication ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawDynamicTruthPiCarrierConstructorEx8BranchCode
        M DTPiEx lowerSigmaApplication)
      (rawFixedFormulaNumeralCode M
        (dynamicTruthPiPrincipalEx8Formula DTPiEx)))
    (rawPiExPrincipalProjectionRoot M hPA inputs context).
Proof.
  intros M hPA witnessList context inputs lowerSigmaApplication
    hcontext hlower.
  rewrite <- (rawDirect_piExPrincipalProjection_identified
    M hPA inputs lowerSigmaApplication hlower).
  change (RawCodedPALocalProofOf M context
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      dynamicTruthPiExPrincipalProjectionTemplateFormula)
    (rawPiExPrincipalProjectionRoot M hPA inputs context)).
  exact (raw_codedPALocalProofOf_binderPrincipalProjectionTemplate
    M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
    witnessList context
    coqDynamicTruthPiExistentialPrefixTemplate
    coqDynamicTruthPiNoBinderCounterexampleTemplate hcontext).
Qed.

(** Assemble the two exact-context endpoints for all eight off-diagonal
    cells.  The direct inputs are consulted only in those cells whose
    branch actually contains the corresponding lower application. *)
Theorem raw_dynamicTruthBinderPrincipalProjectionInterface_of_lower_identification :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context lowerPiApplication lowerSigmaApplication
      (sigmaInputs piInputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedPAAxiomWitnessContext M witnessList context ->
  rawCoqDynamicTruthLowerPiDirectAtomTemplateCode M sigmaInputs =
    lowerPiApplication ->
  rawCoqDynamicTruthLowerSigmaDirectAtomTemplateCode M piInputs =
    lowerSigmaApplication ->
  forall cell,
  RawDynamicTruthBinderPrincipalProjectionInterfaceAt M context cell
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA witnessList context lowerPiApplication
    lowerSigmaApplication sigmaInputs piInputs hcontext
    hsigmaLower hpiLower cell.
  destruct cell;
    unfold RawDynamicTruthBinderPrincipalProjectionInterfaceAt,
      rawDynamicTruthBinderOffDiagonalSigmaBranchCode,
      rawDynamicTruthBinderOffDiagonalPiBranchCode,
      rawDynamicTruthBinderSigmaPrincipalCode,
      rawDynamicTruthBinderPiPrincipalCode;
    cbn [dynamicTruthBinderOffDiagonalSigmaBranch
      dynamicTruthBinderOffDiagonalPiBranch].
  - pose proof (raw_codedPALocalProofOf_sigmaAllPrincipalProjection
      M hPA witnessList context sigmaInputs lowerPiApplication
      hcontext hsigmaLower) as hsigma.
    destruct (raw_codedPALocalProofOf_piFixedPrincipalProjection
      M hPA witnessList context DTPiImp lowerSigmaApplication
      hcontext) as [piRoot hpi]; [discriminate |].
    exists (rawSigmaAllPrincipalProjectionRoot
      M hPA sigmaInputs context), piRoot. split; assumption.
  - pose proof (raw_codedPALocalProofOf_sigmaAllPrincipalProjection
      M hPA witnessList context sigmaInputs lowerPiApplication
      hcontext hsigmaLower) as hsigma.
    destruct (raw_codedPALocalProofOf_piFixedPrincipalProjection
      M hPA witnessList context DTPiAnd lowerSigmaApplication
      hcontext) as [piRoot hpi]; [discriminate |].
    exists (rawSigmaAllPrincipalProjectionRoot
      M hPA sigmaInputs context), piRoot. split; assumption.
  - pose proof (raw_codedPALocalProofOf_sigmaAllPrincipalProjection
      M hPA witnessList context sigmaInputs lowerPiApplication
      hcontext hsigmaLower) as hsigma.
    destruct (raw_codedPALocalProofOf_piFixedPrincipalProjection
      M hPA witnessList context DTPiOr lowerSigmaApplication
      hcontext) as [piRoot hpi]; [discriminate |].
    exists (rawSigmaAllPrincipalProjectionRoot
      M hPA sigmaInputs context), piRoot. split; assumption.
  - pose proof (raw_codedPALocalProofOf_sigmaAllPrincipalProjection
      M hPA witnessList context sigmaInputs lowerPiApplication
      hcontext hsigmaLower) as hsigma.
    pose proof (raw_codedPALocalProofOf_piExPrincipalProjection
      M hPA witnessList context piInputs lowerSigmaApplication
      hcontext hpiLower) as hpi.
    exists (rawSigmaAllPrincipalProjectionRoot
      M hPA sigmaInputs context),
      (rawPiExPrincipalProjectionRoot M hPA piInputs context).
    split; assumption.
  - destruct (raw_codedPALocalProofOf_sigmaFixedPrincipalProjection
      M hPA witnessList context DTSigmaImpFalseLeft lowerPiApplication
      hcontext) as [sigmaRoot hsigma]; [discriminate |].
    pose proof (raw_codedPALocalProofOf_piExPrincipalProjection
      M hPA witnessList context piInputs lowerSigmaApplication
      hcontext hpiLower) as hpi.
    exists sigmaRoot,
      (rawPiExPrincipalProjectionRoot M hPA piInputs context).
    split; assumption.
  - destruct (raw_codedPALocalProofOf_sigmaFixedPrincipalProjection
      M hPA witnessList context DTSigmaImpTrueRight lowerPiApplication
      hcontext) as [sigmaRoot hsigma]; [discriminate |].
    pose proof (raw_codedPALocalProofOf_piExPrincipalProjection
      M hPA witnessList context piInputs lowerSigmaApplication
      hcontext hpiLower) as hpi.
    exists sigmaRoot,
      (rawPiExPrincipalProjectionRoot M hPA piInputs context).
    split; assumption.
  - destruct (raw_codedPALocalProofOf_sigmaFixedPrincipalProjection
      M hPA witnessList context DTSigmaAnd lowerPiApplication
      hcontext) as [sigmaRoot hsigma]; [discriminate |].
    pose proof (raw_codedPALocalProofOf_piExPrincipalProjection
      M hPA witnessList context piInputs lowerSigmaApplication
      hcontext hpiLower) as hpi.
    exists sigmaRoot,
      (rawPiExPrincipalProjectionRoot M hPA piInputs context).
    split; assumption.
  - destruct (raw_codedPALocalProofOf_sigmaFixedPrincipalProjection
      M hPA witnessList context DTSigmaOr lowerPiApplication
      hcontext) as [sigmaRoot hsigma]; [discriminate |].
    pose proof (raw_codedPALocalProofOf_piExPrincipalProjection
      M hPA witnessList context piInputs lowerSigmaApplication
      hcontext hpiLower) as hpi.
    exists sigmaRoot,
      (rawPiExPrincipalProjectionRoot M hPA piInputs context).
    split; assumption.
Qed.

(** Convenient row-graph wrapper.  It deliberately forgets the domain
    equalities from the two direct-identification records, documenting that
    principal projection is independent of the row-domain witnesses. *)
Corollary raw_dynamicTruthBinderPrincipalProjectionInterface_of_direct :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context lowerPiApplication lowerSigmaApplication
      sigmaDomain piDomain
      (sigmaInputs piInputs : RawCodedTemplateDirectStructuralInputs M),
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M sigmaInputs
    sigmaDomain lowerPiApplication ->
  RawCoqDynamicTruthPiDirectTemplateIdentification M piInputs
    piDomain lowerSigmaApplication ->
  forall cell,
  RawDynamicTruthBinderPrincipalProjectionInterfaceAt M context cell
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA witnessList context lowerPiApplication
    lowerSigmaApplication sigmaDomain piDomain sigmaInputs piInputs
    hcontext hsigma hpi cell.
  exact
    (raw_dynamicTruthBinderPrincipalProjectionInterface_of_lower_identification
      M hPA witnessList context lowerPiApplication lowerSigmaApplication
      sigmaInputs piInputs hcontext
      (rawCoqDynamicTruthSigmaDirect_lowerApplication_identified hsigma)
      (rawCoqDynamicTruthPiDirect_lowerApplication_identified hpi)
      cell).
Qed.

(** Native row traces are the narrow operational boundary above the direct
    translator.  They construct both direct-input packages, after which the
    row domains disappear and only their lower-application identifications
    are retained by the projection interface. *)
Theorem raw_dynamicTruthBinderPrincipalProjectionInterface_of_native_traces :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context level upperNumeral
      globalPiCode globalSigmaCode sigmaDomain piDomain
      lowerPiApplication lowerSigmaApplication
      (sigmaSelector : RawCodedTernaryApplicationSelector M globalPiCode)
      (piSelector : RawCodedTernaryApplicationSelector M globalSigmaCode),
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
    globalPiCode sigmaSelector ->
  RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
    globalSigmaCode piSelector ->
  RawNumeralTermCodeAt M (raw_succ M level) upperNumeral ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
    sigmaDomain ->
  RawDynamicTruthCoqLowerApplication M globalPiCode lowerPiApplication ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
    piDomain ->
  RawDynamicTruthPiCoqLowerApplication M
    globalSigmaCode lowerSigmaApplication ->
  forall cell,
  RawDynamicTruthBinderPrincipalProjectionInterfaceAt M context cell
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA witnessList context level upperNumeral
    globalPiCode globalSigmaCode sigmaDomain piDomain
    lowerPiApplication lowerSigmaApplication sigmaSelector piSelector
    hcontext hsigmaCommuting hpiCommuting hupperNumeral
    hsigmaDomain hsigmaLower hpiDomain hpiLower cell.
  destruct
    (rawDynamicTruthSigmaRestrictedUniversalDirectCompiler_of_selector
      M hPA globalPiCode level upperNumeral sigmaDomain
      lowerPiApplication sigmaSelector hsigmaCommuting hupperNumeral
      hsigmaDomain hsigmaLower) as [sigmaInputs hsigmaIdentification].
  destruct
    (raw_coqDynamicTruthPiDirectTemplateIdentification_exists
      M hPA level (raw_succ M level) globalSigmaCode upperNumeral
      piDomain lowerSigmaApplication piSelector hpiCommuting
      hupperNumeral hpiDomain hpiLower) as
    [piInputs hpiIdentification].
  exact (raw_dynamicTruthBinderPrincipalProjectionInterface_of_direct
    M hPA witnessList context lowerPiApplication lowerSigmaApplication
    sigmaDomain piDomain sigmaInputs piInputs hcontext
    hsigmaIdentification hpiIdentification cell).
Qed.

(** Deep three-variable closure supplies the two selector commuting laws.
    This endpoint makes the logical resource explicit: atomic adequacy is
    used only to choose a relational application output; deep shift and
    substitution fixed points prove that the choice commutes with template
    renaming and opening. *)
Corollary raw_dynamicTruthBinderPrincipalProjectionInterface_of_deepClosed :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      witnessList context level upperNumeral
      globalPiCode globalSigmaCode sigmaDomain piDomain
      lowerPiApplication lowerSigmaApplication,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawCodedTernaryPredicateDeepClosed M globalPiCode ->
  RawCodedTernaryPredicateDeepClosed M globalSigmaCode ->
  RawNumeralTermCodeAt M (raw_succ M level) upperNumeral ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode)
    sigmaDomain ->
  RawDynamicTruthCoqLowerApplication M globalPiCode lowerPiApplication ->
  RawCodedFormulaSingleSubstitution M upperNumeral
    (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
    piDomain ->
  RawDynamicTruthPiCoqLowerApplication M
    globalSigmaCode lowerSigmaApplication ->
  forall cell,
  RawDynamicTruthBinderPrincipalProjectionInterfaceAt M context cell
    lowerPiApplication lowerSigmaApplication.
Proof.
  intros M hPA witnessList context level upperNumeral
    globalPiCode globalSigmaCode sigmaDomain piDomain
    lowerPiApplication lowerSigmaApplication hcontext
    hglobalPiDeep hglobalSigmaDeep hupperNumeral
    hsigmaDomain hsigmaLower hpiDomain hpiLower cell.
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    globalPiCode (proj1 hglobalPiDeep)) as [sigmaSelector _].
  destruct (raw_codedTernaryApplicationSelector_exists M hPA
    globalSigmaCode (proj1 hglobalSigmaDeep)) as [piSelector _].
  assert (hsigmaCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
        globalPiCode sigmaSelector).
  {
    constructor.
    - exact (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA globalPiCode sigmaSelector
        (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
          M hPA globalPiCode hglobalPiDeep)).
    - exact
        (rawTernaryApplicationSelector_opening_commuting_on_syntax_of_deepClosed_concrete
          M hPA globalPiCode sigmaSelector hglobalPiDeep).
  }
  assert (hpiCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax M
        globalSigmaCode piSelector).
  {
    constructor.
    - exact (rawTernaryApplicationSelector_shift_commuting_on_syntax
        M hPA globalSigmaCode piSelector
        (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
          M hPA globalSigmaCode hglobalSigmaDeep)).
    - exact
        (rawTernaryApplicationSelector_opening_commuting_on_syntax_of_deepClosed_concrete
          M hPA globalSigmaCode piSelector hglobalSigmaDeep).
  }
  exact
    (raw_dynamicTruthBinderPrincipalProjectionInterface_of_native_traces
      M hPA witnessList context level upperNumeral
      globalPiCode globalSigmaCode sigmaDomain piDomain
      lowerPiApplication lowerSigmaApplication sigmaSelector piSelector
      hcontext hsigmaCommuting hpiCommuting hupperNumeral
      hsigmaDomain hsigmaLower hpiDomain hpiLower cell).
Qed.

End PABoundedRawCodedDynamicTruthBinderPrincipalProjectionCompilation.
