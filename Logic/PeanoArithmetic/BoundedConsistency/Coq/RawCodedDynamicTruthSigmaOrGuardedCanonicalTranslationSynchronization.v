(**
  One direct translation for canonical Sigma/Or rows and guarded evidence.

  The historical guarded-evidence input package cannot itself identify the
  first canonical successor row: its local-exclusivity record requires the
  lower and upper hierarchy names to coincide at zero, whereas that row
  requires lower zero and upper one.  The downstream guarded append bridge,
  however, consumes only the two guarded evidence atoms and the append bound;
  it does not consume the local domain equalities or level alignment.

  This module records that smaller honest interface.  Predicate names zero
  and one retain the two guarded local evidence selectors, names two and
  three select the global Pi/Sigma base predicates used by the canonical
  successor rows, and all remaining opaque names denote bottom.  A corrected
  numeral namespace independently assigns lower=0, upper=1, append mode=0,
  and append bound=0.  Thus a single direct structural translation realizes
  both sides of the formerly cross-translation boundary.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedFormulaOperationsStandardRealization
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedTemplateNumeralParameters
  RawCodedTemplateNumeralTermSyntax
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTernaryPredicateDeepClosure
  RawCodedDynamicTruthTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessTemplateDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedDirectInputs
  RawCodedRestrictedPADerivationSoundnessExtendedRowIdentification
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthGlobalBaseRootClosure
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration
  RawCodedDynamicTruthSigmaOrCanonicalProductionIdentification
  RawCodedDynamicTruthSigmaOrCanonicalTranslationCorrection.

Module
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalTranslationSynchronization.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedFormulaOperationsStandardRealization.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import PABoundedRawCodedTemplateNumeralParameters.
Import PABoundedRawCodedTemplateNumeralTermSyntax.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedDynamicTruthTemplateDirectInputs.
Import PABoundedRawCodedRestrictedPADerivationSoundnessTemplateDirectInputs.
Import PABoundedRawCodedRestrictedPADerivationSoundnessExtendedDirectInputs.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessExtendedRowIdentification.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import PABoundedRawCodedDynamicTruthGlobalBaseRootClosure.
Import PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthZeroLocalExclusiveTemplateIdentification.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import
  PABoundedRawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration.
Import
  PABoundedRawCodedDynamicTruthSigmaOrCanonicalProductionIdentification.
Import
  PABoundedRawCodedDynamicTruthSigmaOrCanonicalTranslationCorrection.

(** These are the literal guarded openings used by the implication and
    Boolean clients: child [#2], assignment code [#6], assignment step [#5].
    Stating the two opaque leaves locally keeps this synchronization layer
    independent of the much larger guarded proof compiler. *)
Definition coqDynamicTruthSigmaOrGuardedLocalSigmaEvidenceTemplate
    : TemplateFormula :=
  tfOpaque coqDynamicTruthLocalSigmaEvidencePredicateName
    [ttVar 2; ttVar 6; ttVar 5].

Definition coqDynamicTruthSigmaOrGuardedLocalPiEvidenceTemplate
    : TemplateFormula :=
  tfOpaque coqDynamicTruthLocalPiEvidencePredicateName
    [ttVar 2; ttVar 6; ttVar 5].

(** Four exact-arity ternary families in one opaque namespace. *)
Definition rawCoqDynamicTruthGuardedCanonicalFourTernaryCode
    {M : RawPAModel}
    {localSigmaCode localPiCode lowerPiCode lowerSigmaCode : M}
    (localSigmaSelector :
      RawCodedTernaryApplicationSelector M localSigmaCode)
    (localPiSelector :
      RawCodedTernaryApplicationSelector M localPiCode)
    (lowerPiSelector :
      RawCodedTernaryApplicationSelector M lowerPiCode)
    (lowerSigmaSelector :
      RawCodedTernaryApplicationSelector M lowerSigmaCode)
    (predicate : TemplatePredicateName) (arguments : list M) : M :=
  match predicate with
  | 0 => rawCoqRestrictedPATernaryDirectSelectorCode
      localSigmaSelector arguments
  | 1 => rawCoqRestrictedPATernaryDirectSelectorCode
      localPiSelector arguments
  | 2 => rawCoqRestrictedPATernaryDirectSelectorCode
      lowerPiSelector arguments
  | 3 => rawCoqRestrictedPATernaryDirectSelectorCode
      lowerSigmaSelector arguments
  | _ => rawFormulaBotCode M
  end.

Arguments rawCoqDynamicTruthGuardedCanonicalFourTernaryCode
  {M localSigmaCode localPiCode lowerPiCode lowerSigmaCode}
  _ _ _ _ _ _.

(** Package the four-way dispatch with the syntax-restricted operation laws
    already supplied by each selected ternary application. *)
Definition rawCoqDynamicTruthGuardedCanonicalFourTernaryDirectSelector
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (localSigmaCode localPiCode lowerPiCode lowerSigmaCode : M)
    (localSigmaSelector :
      RawCodedTernaryApplicationSelector M localSigmaCode)
    (localPiSelector :
      RawCodedTernaryApplicationSelector M localPiCode)
    (lowerPiSelector :
      RawCodedTernaryApplicationSelector M lowerPiCode)
    (lowerSigmaSelector :
      RawCodedTernaryApplicationSelector M lowerSigmaCode)
    (localSigmaCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
        M localSigmaCode localSigmaSelector)
    (localPiCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
        M localPiCode localPiSelector)
    (lowerPiCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
        M lowerPiCode lowerPiSelector)
    (lowerSigmaCommuting :
      RawCoqDynamicTruthTemplateTernaryCommutingOnSyntax
        M lowerSigmaCode lowerSigmaSelector)
    : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters.
Proof.
  refine
    {| rawCoqRestrictedPAOpaqueTailOutput :=
         rawCoqDynamicTruthGuardedCanonicalFourTernaryCode
           localSigmaSelector localPiSelector
           lowerPiSelector lowerSigmaSelector |}.
  - intros depth [|[|[|[|predicate]]]] arguments;
      cbn [rawCoqDynamicTruthGuardedCanonicalFourTernaryCode].
    + apply rawCoqRestrictedPATernaryDirectSelectorCode_shiftAt;
        assumption.
    + apply rawCoqRestrictedPATernaryDirectSelectorCode_shiftAt;
        assumption.
    + apply rawCoqRestrictedPATernaryDirectSelectorCode_shiftAt;
        assumption.
    + apply rawCoqRestrictedPATernaryDirectSelectorCode_shiftAt;
        assumption.
    + apply raw_coqRestrictedPADerivationSoundness_bottom_shift.
      exact hPA.
  - intros depth replacement [|[|[|[|predicate]]]] arguments;
      cbn [rawCoqDynamicTruthGuardedCanonicalFourTernaryCode].
    + apply rawCoqRestrictedPATernaryDirectSelectorCode_openingAt;
        assumption.
    + apply rawCoqRestrictedPATernaryDirectSelectorCode_openingAt;
        assumption.
    + apply rawCoqRestrictedPATernaryDirectSelectorCode_openingAt;
        assumption.
    + apply rawCoqRestrictedPATernaryDirectSelectorCode_openingAt;
        assumption.
    + apply raw_coqRestrictedPADerivationSoundness_bottom_opening.
      exact hPA.
Defined.

Arguments rawCoqDynamicTruthGuardedCanonicalFourTernaryDirectSelector
  M _ _ _ _ _ _ _ _ _ _ _ _ _ _ : clear implicits.

(** A direct-input adapter for an arbitrary opaque selector whose laws use
    the shared numeral-parameter term view. *)
Definition rawCoqDynamicTruthGuardedCanonicalTemplateSymbols
    (M : RawPAModel) (parameters : RawCodedTemplateNumeralParameters M)
    (opaque : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
    : RawCodedTemplateStructuralSymbols M :=
  rawNumeralTemplateSymbols M parameters
    (rawCoqRestrictedPAOpaqueTailOutput opaque).

Lemma rawCoqDynamicTruthGuardedCanonicalTemplateTerm_symbols : forall
    M parameters
      (opaque : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      input,
  rawStructuralTemplateTermWith M
      (rawCoqDynamicTruthGuardedCanonicalTemplateSymbols
        M parameters opaque) input =
    rawCoqRestrictedPADerivationSoundnessTemplateTermView
      M parameters input.
Proof.
  intros M parameters opaque input.
  induction input as
      [index | name | | child IHchild
      | lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs];
    cbn [rawCoqDynamicTruthGuardedCanonicalTemplateSymbols
      rawCoqRestrictedPADerivationSoundnessTemplateTermView
      rawCoqRestrictedPADerivationSoundnessTermViewSymbols
      rawStructuralTemplateTermWith rawNumeralTemplateSymbols];
    try rewrite IHchild; try rewrite IHlhs, IHrhs; reflexivity.
Qed.

Lemma rawCoqDynamicTruthGuardedCanonicalTemplateTerms_symbols : forall
    M parameters
      (opaque : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
      inputs,
  rawStructuralTemplateTermsWith M
      (rawCoqDynamicTruthGuardedCanonicalTemplateSymbols
        M parameters opaque) inputs =
    rawCoqRestrictedPADerivationSoundnessTemplateTermsView
      M parameters inputs.
Proof.
  intros M parameters opaque inputs.
  unfold rawStructuralTemplateTermsWith,
    rawCoqRestrictedPADerivationSoundnessTemplateTermsView.
  apply map_ext. intro input.
  apply rawCoqDynamicTruthGuardedCanonicalTemplateTerm_symbols.
Qed.

Definition rawCoqDynamicTruthGuardedCanonicalDirectStructuralInputs
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (opaque : RawCoqRestrictedPAOpaqueTailDirectSelector M parameters)
    : RawCodedTemplateDirectStructuralInputs M.
Proof.
  refine
    {| rawDirectTemplateSymbols :=
         rawCoqDynamicTruthGuardedCanonicalTemplateSymbols
           M parameters opaque;
       rawDirectTemplateTermShiftAt := _;
       rawDirectTemplateTermOpeningAt := _;
       rawDirectTemplateOpaqueShiftAt := _;
       rawDirectTemplateOpaqueOpeningAt := _ |}.
  - apply raw_numeralTemplateTerm_shift. exact hPA.
  - apply raw_numeralTemplateTerm_substitutionAtom. exact hPA.
  - intros depth predicate arguments.
    cbn [rawCoqDynamicTruthGuardedCanonicalTemplateSymbols
      rawStructuralTemplateFormulaWith templateFormulaRename].
    rewrite !rawCoqDynamicTruthGuardedCanonicalTemplateTerms_symbols.
    apply rawCoqRestrictedPAOpaqueTailShiftAt.
  - intros depth replacement predicate arguments.
    cbn [rawCoqDynamicTruthGuardedCanonicalTemplateSymbols
      rawStructuralTemplateFormulaWith templateFormulaSubst].
    rewrite rawCoqDynamicTruthGuardedCanonicalTemplateTerm_symbols.
    rewrite !rawCoqDynamicTruthGuardedCanonicalTemplateTerms_symbols.
    apply rawCoqRestrictedPAOpaqueTailOpeningAt.
Defined.

Arguments rawCoqDynamicTruthGuardedCanonicalDirectStructuralInputs
  M _ _ _ : clear implicits.

(** The native guarded-coordinate renaming. *)
Definition dynamicTruthSigmaOrGuardedCanonicalEvidenceRenaming
    (index : nat) : nat :=
  match index with
  | 0 => 5
  | 1 => 6
  | 2 => 2
  | S (S (S outer)) => S (S (S outer))
  end.

Lemma dynamicTruthZeroSigmaPredicateFormula_sigmaOr_guarded_application :
  standardTernaryApplication dynamicTruthZeroSigmaPredicateFormula
      (tVar 2) (tVar 6) (tVar 5) =
  Formula.rename dynamicTruthSigmaOrGuardedCanonicalEvidenceRenaming
    dynamicTruthZeroSigmaEvidenceFormula.
Proof. vm_compute. reflexivity. Qed.

Lemma dynamicTruthZeroPiPredicateFormula_sigmaOr_guarded_application :
  standardTernaryApplication dynamicTruthZeroPiPredicateFormula
      (tVar 2) (tVar 6) (tVar 5) =
  Formula.rename dynamicTruthSigmaOrGuardedCanonicalEvidenceRenaming
    dynamicTruthZeroPiEvidenceFormula.
Proof. vm_compute. reflexivity. Qed.

(** Standard quotation fixes the output of any selected represented ternary
    application on three honest quoted terms. *)
Lemma rawTernaryApplicationOutput_sigmaOr_quoted_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      predicate (selector : RawCodedTernaryApplicationSelector M
        (rawQuotedFormulaCode M predicate)) first second third,
  RawCodedTermSyntax M (rawQuotedTermCode M first) ->
  RawCodedTermSyntax M (rawQuotedTermCode M second) ->
  RawCodedTermSyntax M (rawQuotedTermCode M third) ->
  rawTernaryApplicationOutput selector
      (rawQuotedTermCode M first)
      (rawQuotedTermCode M second)
      (rawQuotedTermCode M third) =
  rawQuotedFormulaCode M
    (standardTernaryApplication predicate first second third).
Proof.
  intros M hPA predicate selector first second third
    hfirst hsecond hthird.
  apply (rawTernaryApplicationOutput_unique M hPA
    (rawQuotedFormulaCode M predicate) selector
    (rawQuotedTermCode M first)
    (rawQuotedTermCode M second)
    (rawQuotedTermCode M third)); try assumption.
  exact (raw_codedTernaryApplication_standard M hPA
    predicate first second third).
Qed.

(** Exactly the fields consumed jointly by the canonical append and guarded
    evidence endpoints.  It intentionally omits the incompatible local
    domain and lower=upper alignment fields of the older guarded record. *)
Record RawDynamicTruthSigmaOrGuardedCanonicalTranslationIdentification
    (M : RawPAModel)
    (inputs : RawCodedTemplateDirectStructuralInputs M) : Prop := {
  rawDynamicTruthSigmaOrGuardedCanonical_lowerZero :
    rawDirectTemplateTerm inputs coqDynamicTruthLowerLevelTerm =
      rawQuotedTermCode M (Term.numeral 0);
  rawDynamicTruthSigmaOrGuardedCanonical_upperOne :
    rawDirectTemplateTerm inputs coqDynamicTruthUpperLevelTerm =
      rawQuotedTermCode M (Term.numeral 1);
  rawDynamicTruthSigmaOrGuardedCanonical_modeZero :
    rawDirectTemplateTerm inputs
        (ttParameter coqFourStateTableAppendRowModeParameterName) =
      rawQuotedTermCode M (Term.numeral 0);
  rawDynamicTruthSigmaOrGuardedCanonical_appendBoundZero :
    rawDirectTemplateTerm inputs
        (ttParameter coqDynamicTruthAppendRowBoundParameterName) =
      rawQuotedTermCode M (Term.numeral 0);
  rawDynamicTruthSigmaOrGuardedCanonical_guardedSigma :
    rawDirectTemplateFormula inputs
        coqDynamicTruthSigmaOrGuardedLocalSigmaEvidenceTemplate =
      rawQuotedFormulaCode M
        (Formula.rename
          dynamicTruthSigmaOrGuardedCanonicalEvidenceRenaming
          dynamicTruthZeroSigmaEvidenceFormula);
  rawDynamicTruthSigmaOrGuardedCanonical_guardedPi :
    rawDirectTemplateFormula inputs
        coqDynamicTruthSigmaOrGuardedLocalPiEvidenceTemplate =
      rawQuotedFormulaCode M
        (Formula.rename
          dynamicTruthSigmaOrGuardedCanonicalEvidenceRenaming
          dynamicTruthZeroPiEvidenceFormula);
  rawDynamicTruthSigmaOrGuardedCanonical_sigmaRow :
    rawDirectTemplateFormula inputs
        coqDynamicTruthSharedSigmaSuccessorRowTemplate =
      rawQuotedFormulaCode M
        coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula;
  rawDynamicTruthSigmaOrGuardedCanonical_piRow :
    rawDirectTemplateFormula inputs
        coqDynamicTruthSharedPiSuccessorRowTemplate =
      rawQuotedFormulaCode M
        coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula
}.

Arguments RawDynamicTruthSigmaOrGuardedCanonicalTranslationIdentification
  M inputs : clear implicits.

(** The record's three canonical fields close the complete production-code
    bridge inside this same selector-bearing translation. *)
Theorem
    rawTemplateFormula_sigmaOr_guarded_named_zeroCanonical_eq : forall
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthSigmaOrGuardedCanonicalTranslationIdentification
    M inputs ->
  let translation := rawDirectStructuralTemplateTranslation M hPA inputs in
  rawTemplateFormula translation
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate) =
    rawTemplateFormula translation
      (templateFormulaOpen (embedPATerm (Term.numeral 0))
        (coqFourStateTableAppendEmbeddedModeProductionMotive
          coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula
          coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)).
Proof.
  intros M hPA inputs hidentification translation.
  destruct hidentification as
    [hlower hupper hmode hbound hsigmaEvidence hpiEvidence
      hsigmaRow hpiRow].
  apply
    (rawTemplateFormula_dynamicTruthSigmaOr_named_zeroCanonical_eq
      M translation).
  - change (rawDirectTemplateTerm inputs
      (ttParameter coqFourStateTableAppendRowModeParameterName) =
    rawDirectTemplateTerm inputs (embedPATerm (Term.numeral 0))).
    rewrite hmode.
    reflexivity.
  - change (rawDirectTemplateFormula inputs
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    rawDirectTemplateFormula inputs
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula)).
    rewrite hsigmaRow.
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    reflexivity.
  - change (rawDirectTemplateFormula inputs
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    rawDirectTemplateFormula inputs
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)).
    rewrite hpiRow.
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    reflexivity.
Qed.

(** Consume the three non-mode roots in the synchronized translation.  The
    mode root and all carrier transports are internal consequences of the
    identification record. *)
Theorem
    raw_dynamicTruthZeroCanonicalFixedProductionRoot_of_sigma_or_guarded_synchronized_three_roots :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    sourceWitnessList sourceContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    domainRoot codeRoot leftStateRoot,
  RawDynamicTruthSigmaOrGuardedCanonicalTranslationIdentification
    M inputs ->
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceContext tail)
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceContext tail)
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrOpenedCodeAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) codeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceContext tail)
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrOpenedLeftStateAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) leftStateRoot ->
  exists fixedProductionRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        sourceContext tail)
      (rawTemplateFormula
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (templateFormulaOpen (embedPATerm (Term.numeral 0))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula
            coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)))
      fixedProductionRoot.
Proof.
  intros M hPA inputs sourceWitnessList sourceContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    domainRoot codeRoot leftStateRoot
    hidentification hbase hdomain hcode hleftState.
  destruct hidentification as
    [hlower hupper hmode hbound hsigmaEvidence hpiEvidence
      hsigmaRow hpiRow].
  apply
    (raw_dynamicTruthZeroCanonicalFixedProductionRoot_of_sigma_or_three_roots_and_atomic_identifications
      M hPA (rawDirectStructuralTemplateTranslation M hPA inputs)
      sourceWitnessList sourceContext tail
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0
      domainRoot codeRoot leftStateRoot hbase).
  - change (rawDirectTemplateTerm inputs
      (ttParameter coqFourStateTableAppendRowModeParameterName) =
    rawDirectTemplateTerm inputs (embedPATerm (Term.numeral 0))).
    rewrite hmode. reflexivity.
  - change (rawDirectTemplateFormula inputs
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    rawDirectTemplateFormula inputs
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula)).
    rewrite hsigmaRow.
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    reflexivity.
  - change (rawDirectTemplateFormula inputs
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    rawDirectTemplateFormula inputs
      (embedPAFormula
        coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)).
    rewrite hpiRow.
    unfold rawDirectTemplateFormula.
    rewrite rawStructuralTemplateFormulaWith_embedPA.
    reflexivity.
  - exact hdomain.
  - exact hcode.
  - exact hleftState.
Qed.

(** The old full guarded-identification record cannot be recovered from this
    canonical namespace when the quoted zero and one term codes are distinct:
    that record requires the translated lower and upper terms to coincide. *)
Theorem
    raw_dynamicTruthSigmaOrGuardedCanonical_not_localExclusive_level_aligned :
    forall (M : RawPAModel)
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawDynamicTruthSigmaOrGuardedCanonicalTranslationIdentification
    M inputs ->
  rawQuotedTermCode M (Term.numeral 0) <>
    rawQuotedTermCode M (Term.numeral 1) ->
  forall sigmaDomain piDomain sigmaEvidence piEvidence,
  ~ RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
      sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M inputs
    [hlower hupper hmode hbound hsigmaEvidence hpiEvidence
      hsigmaRow hpiRow]
    hcodesDistinct sigmaDomain piDomain sigmaEvidence piEvidence
    hlocalExclusive.
  apply hcodesDistinct.
  rewrite <- hlower, <- hupper.
  exact (rawCoqDynamicTruthLocalExclusive_levelAlignment
    M inputs sigmaDomain piDomain sigmaEvidence piEvidence
    hlocalExclusive).
Qed.

(** Construct the synchronized input package. *)
Theorem
    raw_dynamicTruthSigmaOrGuardedCanonicalTranslationIdentification_exists :
    forall (M : RawPAModel), RawPASatisfies M ->
  exists inputs : RawCodedTemplateDirectStructuralInputs M,
    RawDynamicTruthSigmaOrGuardedCanonicalTranslationIdentification
      M inputs.
Proof.
  intros M hPA.
  pose proof
    (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthZeroSigmaPredicateFormula
      dynamicTruthZeroSigmaPredicateFormula_scoped) as hlocalSigmaDeep.
  pose proof
    (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthZeroPiPredicateFormula
      dynamicTruthZeroPiPredicateFormula_scoped) as hlocalPiDeep.
  pose proof
    (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthGlobalPiBaseFormula
      dynamicTruthGlobalPiBaseFormula_scoped) as hlowerPiDeep.
  pose proof
    (raw_quotedFormula_ternaryPredicateDeepClosed M hPA
      dynamicTruthGlobalSigmaBaseFormula
      dynamicTruthGlobalSigmaBaseFormula_scoped) as hlowerSigmaDeep.
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
      hlocalSigmaDeep) as [localSigmaSelector localSigmaCommuting].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
      hlocalPiDeep) as [localPiSelector localPiCommuting].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
      hlowerPiDeep) as [lowerPiSelector lowerPiCommuting].
  destruct
    (raw_coqDynamicTruthTemplateTernarySelector_exists_of_deepClosed
      M hPA (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
      hlowerSigmaDeep) as [lowerSigmaSelector lowerSigmaCommuting].
  set (parameters :=
    rawDynamicTruthSigmaOrCanonicalNumeralParameters M hPA).
  set (opaque :=
    rawCoqDynamicTruthGuardedCanonicalFourTernaryDirectSelector
      M hPA parameters
      (rawQuotedFormulaCode M dynamicTruthZeroSigmaPredicateFormula)
      (rawQuotedFormulaCode M dynamicTruthZeroPiPredicateFormula)
      (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
      (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
      localSigmaSelector localPiSelector
      lowerPiSelector lowerSigmaSelector
      localSigmaCommuting localPiCommuting
      lowerPiCommuting lowerSigmaCommuting).
  set (inputs :=
    rawCoqDynamicTruthGuardedCanonicalDirectStructuralInputs
      M hPA parameters opaque).

  assert (hterm2 : RawCodedTermSyntax M
      (rawQuotedTermCode M (tVar 2))).
  {
    change (RawCodedTermSyntax M
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters (ttVar 2))).
    apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  }
  assert (hterm6 : RawCodedTermSyntax M
      (rawQuotedTermCode M (tVar 6))).
  {
    change (RawCodedTermSyntax M
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters (ttVar 6))).
    apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  }
  assert (hterm5 : RawCodedTermSyntax M
      (rawQuotedTermCode M (tVar 5))).
  {
    change (RawCodedTermSyntax M
      (rawCoqRestrictedPADerivationSoundnessTemplateTermView
        M parameters (ttVar 5))).
    apply rawCoqRestrictedPADerivationSoundnessTemplateTermView_syntax.
    exact hPA.
  }

  assert (hguardedSigma : rawDirectTemplateFormula inputs
      coqDynamicTruthSigmaOrGuardedLocalSigmaEvidenceTemplate =
    rawQuotedFormulaCode M
      (Formula.rename dynamicTruthSigmaOrGuardedCanonicalEvidenceRenaming
        dynamicTruthZeroSigmaEvidenceFormula)).
  {
    change
      (rawTernaryApplicationOutput localSigmaSelector
        (rawQuotedTermCode M (tVar 2))
        (rawQuotedTermCode M (tVar 6))
        (rawQuotedTermCode M (tVar 5)) = _).
    rewrite <-
      dynamicTruthZeroSigmaPredicateFormula_sigmaOr_guarded_application.
    apply (rawTernaryApplicationOutput_sigmaOr_quoted_standard M hPA);
      assumption.
  }
  assert (hguardedPi : rawDirectTemplateFormula inputs
      coqDynamicTruthSigmaOrGuardedLocalPiEvidenceTemplate =
    rawQuotedFormulaCode M
      (Formula.rename dynamicTruthSigmaOrGuardedCanonicalEvidenceRenaming
        dynamicTruthZeroPiEvidenceFormula)).
  {
    change
      (rawTernaryApplicationOutput localPiSelector
        (rawQuotedTermCode M (tVar 2))
        (rawQuotedTermCode M (tVar 6))
        (rawQuotedTermCode M (tVar 5)) = _).
    rewrite <-
      dynamicTruthZeroPiPredicateFormula_sigmaOr_guarded_application.
    apply (rawTernaryApplicationOutput_sigmaOr_quoted_standard M hPA);
      assumption.
  }

  set (contextTruth :=
    rawBottomRestrictedPATruthDirectSelector M hPA parameters).
  set (conclusionTruth :=
    rawBottomRestrictedPATruthDirectSelector M hPA parameters).
  set (rowInputs := rawCoqRestrictedPAExtendedRowsInputs
    M hPA parameters contextTruth conclusionTruth
    (raw_zero M) (raw_succ M (raw_zero M))
    (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
    (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
    lowerPiSelector lowerSigmaSelector
    lowerPiCommuting lowerSigmaCommuting eq_refl eq_refl).
  set (upperNumeral := rawQuotedTermCode M (Term.numeral 1)).
  set (sigmaDomain := rawQuotedFormulaCode M
    (dynamicTruthSigmaRowInstantiatedDomain (Term.numeral 1))).
  set (piDomain := rawQuotedFormulaCode M
    (dynamicTruthPiRowInstantiatedDomain (Term.numeral 1))).
  set (sigmaLowerApplication := rawQuotedFormulaCode M
    (Formula.rename dynamicTruthCoqLowerApplicationRenaming
      dynamicTruthGlobalPiBaseFormula)).
  set (piLowerApplication := rawQuotedFormulaCode M
    (Formula.rename dynamicTruthPiCoqLowerApplicationRenaming
      dynamicTruthGlobalSigmaBaseFormula)).
  assert (hsigmaDomain : RawCodedFormulaSingleSubstitution M
      upperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthSigmaRowDomainTemplate))
      sigmaDomain).
  {
    unfold upperNumeral, sigmaDomain.
    exact (raw_dynamicTruthSigmaRowInstantiatedDomain_standard
      M hPA (Term.numeral 1)).
  }
  assert (hpiDomain : RawCodedFormulaSingleSubstitution M
      upperNumeral
      (rawNumeralValue M
        (formulaCode dynamicTruthPiRowDomainTemplate))
      piDomain).
  {
    unfold upperNumeral, piDomain,
      dynamicTruthPiRowInstantiatedDomain.
    rewrite <- (rawQuotedTermCode_standard M hPA (Term.numeral 1)).
    rewrite <- (rawQuotedFormulaCode_standard M hPA
      dynamicTruthPiRowDomainTemplate).
    exact (raw_codedFormulaSingleSubstitution_standard M hPA
      (Term.numeral 1) dynamicTruthPiRowDomainTemplate).
  }
  assert (hsigmaLower : RawDynamicTruthCoqLowerApplication M
      (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
      sigmaLowerApplication).
  {
    unfold sigmaLowerApplication.
    exact (raw_dynamicTruthCoqLowerApplication_standard_rename
      M hPA dynamicTruthGlobalPiBaseFormula
      dynamicTruthGlobalPiBaseFormula_scoped).
  }
  assert (hpiLower : RawDynamicTruthPiCoqLowerApplication M
      (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
      piLowerApplication).
  {
    unfold piLowerApplication.
    exact (raw_dynamicTruthPiCoqLowerApplication_standard_rename
      M hPA dynamicTruthGlobalSigmaBaseFormula
      dynamicTruthGlobalSigmaBaseFormula_scoped).
  }
  pose proof
    (raw_coqRestrictedPAExtendedRows_identify_native
      M hPA parameters contextTruth conclusionTruth
      (raw_zero M) (raw_succ M (raw_zero M))
      (rawQuotedFormulaCode M dynamicTruthGlobalPiBaseFormula)
      (rawQuotedFormulaCode M dynamicTruthGlobalSigmaBaseFormula)
      lowerPiSelector lowerSigmaSelector
      lowerPiCommuting lowerSigmaCommuting
      eq_refl eq_refl
      upperNumeral sigmaDomain piDomain
      sigmaLowerApplication piLowerApplication
      (rawDynamicTruthSigmaOrCanonicalParameters_upper_one M hPA)
      hsigmaDomain hpiDomain hsigmaLower hpiLower) as hrows.
  destruct hrows as [hsigmaRow hpiRow].

  assert (hsigmaInput : rawDirectTemplateFormula inputs
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    rawDirectTemplateFormula rowInputs
      coqDynamicTruthSharedSigmaSuccessorRowTemplate).
  {
    reflexivity.
  }
  assert (hpiInput : rawDirectTemplateFormula inputs
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    rawDirectTemplateFormula rowInputs
      coqDynamicTruthSharedPiSuccessorRowTemplate).
  {
    reflexivity.
  }
  assert (hsigma : rawDirectTemplateFormula inputs
      coqDynamicTruthSharedSigmaSuccessorRowTemplate =
    rawQuotedFormulaCode M
      coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula).
  {
    rewrite hsigmaInput.
    etransitivity; [exact hsigmaRow |].
    unfold sigmaDomain, sigmaLowerApplication,
      coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula.
    apply rawDynamicTruthSigmaSuccessorRowCode_quoted.
    exact hPA.
  }
  assert (hpi : rawDirectTemplateFormula inputs
      coqDynamicTruthSharedPiSuccessorRowTemplate =
    rawQuotedFormulaCode M
      coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula).
  {
    rewrite hpiInput.
    etransitivity; [exact hpiRow |].
    unfold piDomain, piLowerApplication,
      coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula.
    apply rawDynamicTruthPiSuccessorRowCode_quoted.
    exact hPA.
  }

  exists inputs. constructor.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact hguardedSigma.
  - exact hguardedPi.
  - exact hsigma.
  - exact hpi.
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalTranslationSynchronization.
