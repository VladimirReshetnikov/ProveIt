(**
  Feed the finite Sigma/Or proof template into the append compiler.

  [RawCodedDynamicTruthSigmaOrFixedProductionTemplate] deliberately proves
  its result from a four-formula context.  Native clients, however, obtain
  those four formulas as independently compiled roots: the selected mode,
  the instantiated Sigma domain, the parent Or-code atom, and the selected
  left-child state atom need not be literal assumptions in one syntactic
  prefix.

  This file performs the missing represented composition.  First it rebuilds
  the finite proof over an arbitrary caller prefix and curries the four
  assumptions.  The compiled implication is then applied to four represented
  roots in one unchanged context.  Finally the resulting fixed-production
  root is passed to the existing append/global traversal compiler.

  The last theorem also records, without hiding it in a new callback record,
  the exact remaining bridge to the historical rank-zero compiler.  The new
  template targets the shared named-row formula, whereas that compiler asks
  for the opened embedded canonical row.  A single carrier-code equality is
  therefore sufficient for transport once the four source roots exist.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAAxiomWitnessPrefix
  RawCodedTemplateSyntax
  RawCodedTemplatePAEmbedding
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDisjunctionCaseSchemas
  RawCodedFourStateTableAppendProofCompilation
  RawCodedFourStateTableAppendExistentialElimination
  RawCodedFourStateTableAppendRowLtSuccCases
  RawCodedFourStateTableAppendGlobalTraversalAssembly
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph
  RawCodedDynamicTruthPredecessorGlobalExistentialElimination
  RawCodedDynamicTruthSuccessorRowsAppendNormalization
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate.

Module
  PABoundedRawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDisjunctionCaseSchemas.
Import PABoundedRawCodedFourStateTableAppendProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.
Import PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
Import PABoundedRawCodedFourStateTableAppendGlobalTraversalAssembly.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.
Import
  PABoundedRawCodedDynamicTruthPredecessorGlobalExistentialElimination.
Import PABoundedRawCodedDynamicTruthSuccessorRowsAppendNormalization.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.

(** The four source formulas may sit above an arbitrary temporary prefix.
    Keeping their order identical to the small source module makes the four
    subsequent implication introductions a transparent context calculation. *)
Definition coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    (tail : TemplateContext) : TemplateContext :=
  coqDynamicTruthSigmaOrFixedProductionContextAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 ++ tail.

(** Rebuild the finite proof with every proof node carrying the enlarged
    context.  A generic proof-code weakening transformation would have to
    handle eigenvariable shifts for every rule.  This proof uses no All-I or
    Ex-E, so spelling its five constructors directly is both smaller and a
    more auditable account of the context transport. *)
Definition coqDynamicTruthSigmaOrOpenedLeafProofOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  let formulaCode := coqDynamicTruthSigmaOrOpenedCodeAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let leftState := coqDynamicTruthSigmaOrOpenedLeftStateAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let rightState := coqDynamicTruthSigmaOrOpenedRightStateAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  trpAndI context formulaCode (tfOr leftState rightState)
    (trpAss context formulaCode)
    (trpOrI1 context leftState rightState
      (trpAss context leftState)).

Definition coqDynamicTruthSigmaOrOpenedBranchesProofOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  templateRightDisjunctionIntroductionAt context
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    4
    (coqDynamicTruthSigmaOrOpenedLeafProofOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).

Definition coqDynamicTruthSigmaOrOpenedRowBodyProofOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  trpAndI context
    (coqDynamicTruthSigmaOrOpenedDomainAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedBranchesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (trpAss context
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0))
    (coqDynamicTruthSigmaOrOpenedBranchesProofOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).

Definition coqDynamicTruthSigmaOrSuccessorRowProofOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  templateExistentialWitnessIntroductionFrom context
    (coqDynamicTruthSigmaOrWitnessesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    (coqDynamicTruthSigmaOrOpenedRowBodyProofOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).

Definition coqDynamicTruthSigmaOrFixedProductionProofOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail : TemplateRawProof :=
  let context := coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail in
  let sigmaCase := tfAnd coqDynamicTruthSigmaOrModeZeroTemplate
    coqDynamicTruthSharedSigmaSuccessorRowTemplate in
  let piCase := tfAnd coqDynamicTruthSigmaOrModeOneTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate in
  trpOrI1 context sigmaCase piCase
    (trpAndI context coqDynamicTruthSigmaOrModeZeroTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      (trpAss context coqDynamicTruthSigmaOrModeZeroTemplate)
      (coqDynamicTruthSigmaOrSuccessorRowProofOnTailAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0 tail)).

Theorem coqDynamicTruthSigmaOrOpenedLeafProofOnTailAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqDynamicTruthSigmaOrOpenedLeafAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedLeafProofOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros.
  rewrite coqDynamicTruthSigmaOrOpenedLeafAt_shape.
  unfold coqDynamicTruthSigmaOrOpenedLeafProofOnTailAt,
    TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
    coqDynamicTruthSigmaOrFixedProductionContextAt List.app].
  repeat split; auto.
Qed.

Theorem coqDynamicTruthSigmaOrOpenedBranchesProofOnTailAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqDynamicTruthSigmaOrOpenedBranchesAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedBranchesProofOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros.
  unfold coqDynamicTruthSigmaOrOpenedBranchesProofOnTailAt,
    coqDynamicTruthSigmaOrOpenedBranchesAt.
  eapply templateRightDisjunctionIntroductionAt_derives.
  - reflexivity.
  - apply coqDynamicTruthSigmaOrOpenedLeafProofOnTailAt_derives.
Qed.

Theorem coqDynamicTruthSigmaOrOpenedRowBodyProofOnTailAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqDynamicTruthSigmaOrOpenedRowBodyAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedRowBodyProofOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros.
  pose proof
    (coqDynamicTruthSigmaOrOpenedBranchesProofOnTailAt_derives
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail) as hbranches.
  destruct hbranches as [hvalid [hcontext hconclusion]].
  unfold coqDynamicTruthSigmaOrOpenedRowBodyProofOnTailAt,
    coqDynamicTruthSigmaOrOpenedRowBodyAt, TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
    coqDynamicTruthSigmaOrFixedProductionContextAt List.app].
  repeat split; try assumption; auto.
Qed.

Theorem coqDynamicTruthSigmaOrSuccessorRowProofOnTailAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    (coqDynamicTruthSigmaOrSuccessorRowProofOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros.
  apply templateExistentialWitnessIntroductionFrom_derives.
  rewrite coqDynamicTruthSigmaOrOpenedRowBodyAt_exact.
  apply coqDynamicTruthSigmaOrOpenedRowBodyProofOnTailAt_derives.
Qed.

Theorem coqDynamicTruthSigmaOrFixedProductionProofOnTailAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqFourStateTableAppendNamedClosedRowProductionTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (coqDynamicTruthSigmaOrFixedProductionProofOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros.
  pose proof
    (coqDynamicTruthSigmaOrSuccessorRowProofOnTailAt_derives
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail) as hsigma.
  destruct hsigma as [hvalid [hcontext hconclusion]].
  unfold coqDynamicTruthSigmaOrFixedProductionProofOnTailAt,
    coqFourStateTableAppendNamedClosedRowProductionTemplate,
    coqDynamicTruthSigmaOrModeZeroTemplate,
    coqDynamicTruthSigmaOrModeOneTemplate,
    TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
    coqDynamicTruthSigmaOrFixedProductionContextAt List.app].
  repeat split; try assumption; auto.
Qed.

(** Curry the four source assumptions so their represented proofs may have
    been constructed independently. *)
Definition coqDynamicTruthSigmaOrFixedProductionCurriedFormulaAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 : TemplateFormula :=
  tfImp coqDynamicTruthSigmaOrModeZeroTemplate
    (tfImp
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)
      (tfImp
        (coqDynamicTruthSigmaOrOpenedCodeAt
          witness7 witness6 witness5 witness4
          witness3 witness2 witness1 witness0)
        (tfImp
          (coqDynamicTruthSigmaOrOpenedLeftStateAt
            witness7 witness6 witness5 witness4
            witness3 witness2 witness1 witness0)
          (coqFourStateTableAppendNamedClosedRowProductionTemplate
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate)))).

Definition coqDynamicTruthSigmaOrFixedProductionCurriedProofAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    (tail : TemplateContext) : TemplateRawProof :=
  let mode := coqDynamicTruthSigmaOrModeZeroTemplate in
  let domain := coqDynamicTruthSigmaOrOpenedDomainAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let code := coqDynamicTruthSigmaOrOpenedCodeAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let leftState := coqDynamicTruthSigmaOrOpenedLeftStateAt
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 in
  let conclusion := coqFourStateTableAppendNamedClosedRowProductionTemplate
    coqDynamicTruthSharedSigmaSuccessorRowTemplate
    coqDynamicTruthSharedPiSuccessorRowTemplate in
  trpImpI tail mode
    (tfImp domain (tfImp code (tfImp leftState conclusion)))
    (trpImpI (mode :: tail) domain
      (tfImp code (tfImp leftState conclusion))
      (trpImpI (domain :: mode :: tail) code
        (tfImp leftState conclusion)
        (trpImpI (code :: domain :: mode :: tail) leftState conclusion
          (coqDynamicTruthSigmaOrFixedProductionProofOnTailAt
            witness7 witness6 witness5 witness4
            witness3 witness2 witness1 witness0 tail)))).

Lemma templateRawDerives_impI_local : forall
    context antecedent consequent child,
  TemplateRawDerives (antecedent :: context) consequent child ->
  TemplateRawDerives context (tfImp antecedent consequent)
    (trpImpI context antecedent consequent child).
Proof.
  intros context antecedent consequent child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Theorem coqDynamicTruthSigmaOrFixedProductionCurriedProofAt_derives : forall
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0 tail,
  TemplateRawDerives tail
    (coqDynamicTruthSigmaOrFixedProductionCurriedFormulaAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrFixedProductionCurriedProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
Proof.
  intros.
  unfold coqDynamicTruthSigmaOrFixedProductionCurriedProofAt,
    coqDynamicTruthSigmaOrFixedProductionCurriedFormulaAt.
  apply templateRawDerives_impI_local.
  apply templateRawDerives_impI_local.
  apply templateRawDerives_impI_local.
  apply templateRawDerives_impI_local.
  change (TemplateRawDerives
    (coqDynamicTruthSigmaOrFixedProductionContextOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)
    (coqFourStateTableAppendNamedClosedRowProductionTemplate
      coqDynamicTruthSharedSigmaSuccessorRowTemplate
      coqDynamicTruthSharedPiSuccessorRowTemplate)
    (coqDynamicTruthSigmaOrFixedProductionProofOnTailAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail)).
  apply coqDynamicTruthSigmaOrFixedProductionProofOnTailAt_derives.
Qed.

(** The represented four-root handoff.  Unlike a new compiler record, this
    theorem consumes the roots immediately and exposes the generated proof
    root in its conclusion. *)
Theorem
    raw_codedPALocalProofOf_dynamic_truth_sigma_or_fixed_production_of_four_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    witnessList baseContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot leftStateRoot,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      coqDynamicTruthSigmaOrModeZeroTemplate) modeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedCodeAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) codeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedLeftStateAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) leftStateRoot ->
  exists fixedProductionRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        (coqFourStateTableAppendNamedClosedRowProductionTemplate
          coqDynamicTruthSharedSigmaSuccessorRowTemplate
          coqDynamicTruthSharedPiSuccessorRowTemplate))
      fixedProductionRoot.
Proof.
  intros M hPA translation witnessList baseContext tail
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot leftStateRoot
    hbase hmode hdomain hcode hleftState.
  set (curriedProof :=
    coqDynamicTruthSigmaOrFixedProductionCurriedProofAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0 tail).
  pose proof
    (raw_templateProofOnPAAxiomContext_localProof
      M hPA translation witnessList baseContext curriedProof hbase
      (proj1
        (coqDynamicTruthSigmaOrFixedProductionCurriedProofAt_derives
          witness7 witness6 witness5 witness4
          witness3 witness2 witness1 witness0 tail))) as hcurried.
  unfold curriedProof in hcurried.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext tail)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrFixedProductionCurriedFormulaAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) _) in hcurried.
  unfold coqDynamicTruthSigmaOrFixedProductionCurriedFormulaAt in hcurried.
  rewrite !rawTemplateFormula_imp in hcurried.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawTemplateContextCodeOnTail translation baseContext tail)
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrModeZeroTemplate)
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (coqDynamicTruthSigmaOrOpenedDomainAt
            witness7 witness6 witness5 witness4
            witness3 witness2 witness1 witness0))
        (rawFormulaImpCode M
          (rawTemplateFormula translation
            (coqDynamicTruthSigmaOrOpenedCodeAt
              witness7 witness6 witness5 witness4
              witness3 witness2 witness1 witness0))
          (rawFormulaImpCode M
            (rawTemplateFormula translation
              (coqDynamicTruthSigmaOrOpenedLeftStateAt
                witness7 witness6 witness5 witness4
                witness3 witness2 witness1 witness0))
            (rawTemplateFormula translation
              (coqFourStateTableAppendNamedClosedRowProductionTemplate
                coqDynamicTruthSharedSigmaSuccessorRowTemplate
                coqDynamicTruthSharedPiSuccessorRowTemplate)))))
      _ modeRoot hcurried hmode) as hafterMode.
  lazymatch type of hafterMode with
  | RawCodedPALocalProofOf _ _ _ ?afterModeRoot =>
      destruct
        (raw_codedPALocalProofOf_impE3 M hPA
          (rawTemplateContextCodeOnTail translation baseContext tail)
          (rawTemplateFormula translation
            (coqDynamicTruthSigmaOrOpenedDomainAt
              witness7 witness6 witness5 witness4
              witness3 witness2 witness1 witness0))
          (rawTemplateFormula translation
            (coqDynamicTruthSigmaOrOpenedCodeAt
              witness7 witness6 witness5 witness4
              witness3 witness2 witness1 witness0))
          (rawTemplateFormula translation
            (coqDynamicTruthSigmaOrOpenedLeftStateAt
              witness7 witness6 witness5 witness4
              witness3 witness2 witness1 witness0))
          (rawTemplateFormula translation
            (coqFourStateTableAppendNamedClosedRowProductionTemplate
              coqDynamicTruthSharedSigmaSuccessorRowTemplate
              coqDynamicTruthSharedPiSuccessorRowTemplate))
          afterModeRoot domainRoot codeRoot leftStateRoot
          hafterMode hdomain hcode hleftState) as
        [fixedProductionRoot hfixed]
  end.
  exists fixedProductionRoot. exact hfixed.
Qed.

(** Immediate handoff to the completed shared append traversal at mode zero.
    This theorem is intentionally a direct argument list: no new package
    merely renames the four source-root obligation. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_sigma_global_of_append_inherited_and_sigma_or_roots :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot inheritedTraversal oldLookup
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot leftStateRoot,
  let boundName := coqDynamicTruthAppendRowBoundParameterName in
  let namedRowPrefix :=
    coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      (ttParameter boundName)
      (ttParameter coqFourStateTableAppendRowModeParameterName)
      (ttParameter coqFourStateTableAppendRowFormulaParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentCodeParameterName)
      (ttParameter coqFourStateTableAppendRowAssignmentStepParameterName) in
  (forall tail,
    rawTemplateContextCodeOnTail translation tail namedRowPrefix =
    rawTemplateContextCodeOnTail translation tail
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral 0))
        (ttVar 0) (ttVar 1) (ttVar 2))) ->
  RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (rawTemplateFormula translation
      (coqFourStateTableAppendExistsTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        (ttParameter boundName) (embedPATerm (Term.numeral 0))
        (ttVar 0) (ttVar 1) (ttVar 2))) appendRoot ->
  templateUniversalOpenMany inheritedTraversal
      coqFourStateTableAppendConcreteRowVariables =
    Some
      (tfImp
        (coqLtSuccCasesBelowTemplate
          (ttVar 4) (ttParameter boundName))
        (tfImp oldLookup
          (coqFourStateTableAppendConcreteClosedRowProductionTemplate
            coqDynamicTruthSharedSigmaSuccessorRowTemplate
            coqDynamicTruthSharedPiSuccessorRowTemplate))) ->
  RawFourStateTableAppendInheritedLocalRootsAt M translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    namedRowPrefix inheritedTraversal oldLookup ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) namedRowPrefix)
    (rawTemplateFormula translation
      coqDynamicTruthSigmaOrModeZeroTemplate) modeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) namedRowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) namedRowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedCodeAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) codeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)) namedRowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedLeftStateAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) leftStateRoot ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      witnesses (raw_zero M))
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M)) []
    (rawTemplateFormula translation
      (coqDynamicTruthGlobalExistentialSource 0
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate)).
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    witnesses appendRoot inheritedTraversal oldLookup
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot leftStateRoot
    boundName namedRowPrefix hprefix happend hopen hinherited
    hmode hdomain hcode hleftState.
  cbn zeta in *.
  pose proof (raw_templateEmbeddedPAAxiomWitnessContext
    M hPA translation hagreement witnesses) as hbase.
  rewrite (raw_templateContextCode_embedPAAxiomWitnesses
    M translation hagreement witnesses) in hbase.
  destruct
    (raw_codedPALocalProofOf_dynamic_truth_sigma_or_fixed_production_of_four_roots
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      namedRowPrefix
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0
      modeRoot domainRoot codeRoot leftStateRoot
      hbase hmode hdomain hcode hleftState) as
    [fixedProductionRoot hfixed].
  exact
    (raw_codedPAGrowingTemplateLocalProofAt_dynamic_truth_shared_successor_global_of_append_and_inherited_row_roots
      M hPA translation hagreement 0
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      witnesses appendRoot inheritedTraversal oldLookup fixedProductionRoot
      (or_introl eq_refl) hprefix happend hopen hinherited hfixed).
Qed.

(** These are deliberately stated by their literal row bodies rather than
    imported through the much larger native source-identification module.
    They are definitionally the same two formulas called
    [dynamicTruthZeroCanonicalSigmaRowFormula] and
    [dynamicTruthZeroCanonicalPiRowFormula] there.  Keeping the bridge at
    this lightweight syntax layer also makes clear that no theorem from the
    downstream canonical compiler is being smuggled into the construction. *)
Definition coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula : formula :=
  dynamicTruthSigmaSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalPiBaseFormula.

Definition coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula : formula :=
  dynamicTruthPiSuccessorRowFormula (Term.numeral 1)
    dynamicTruthGlobalSigmaBaseFormula.

(** Exact one-context bridge toward the historical canonical compiler.  The
    equality is a code identification, not a proof-producing premise: after
    it is supplied the already constructed proof root is reused verbatim. *)
Theorem
    raw_dynamicTruthZeroCanonicalFixedProductionRootAtRootTermsUnderPrefix_of_sigma_or_roots_and_code_identification :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext
    outerPrefix rootFormula rootAssignmentCode rootAssignmentStep
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot leftStateRoot,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  let rowPrefix := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
      (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0)
      (ttParameter coqDynamicTruthAppendRowBoundParameterName)
      (embedPATerm (Term.numeral 0))
      rootFormula rootAssignmentCode rootAssignmentStep outerPrefix) in
  rawTemplateFormula translation
      (coqFourStateTableAppendNamedClosedRowProductionTemplate
        coqDynamicTruthSharedSigmaSuccessorRowTemplate
        coqDynamicTruthSharedPiSuccessorRowTemplate) =
    rawTemplateFormula translation
      (templateFormulaOpen (embedPATerm (Term.numeral 0))
        (coqFourStateTableAppendEmbeddedModeProductionMotive
          coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula
          coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
    (rawTemplateFormula translation
      coqDynamicTruthSigmaOrModeZeroTemplate) modeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedDomainAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) domainRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedCodeAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) codeRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
    (rawTemplateFormula translation
      (coqDynamicTruthSigmaOrOpenedLeftStateAt
        witness7 witness6 witness5 witness4
        witness3 witness2 witness1 witness0)) leftStateRoot ->
  exists fixedProductionRoot,
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation sourceContext rowPrefix)
      (rawTemplateFormula translation
        (templateFormulaOpen (embedPATerm (Term.numeral 0))
          (coqFourStateTableAppendEmbeddedModeProductionMotive
            coqDynamicTruthSigmaOrZeroCanonicalSigmaRowFormula
            coqDynamicTruthSigmaOrZeroCanonicalPiRowFormula)))
      fixedProductionRoot.
Proof.
  intros M hPA translation sourceWitnessList sourceContext
    outerPrefix rootFormula rootAssignmentCode rootAssignmentStep
    witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0
    modeRoot domainRoot codeRoot leftStateRoot hbase rowPrefix
    hcodeIdentification hmode hdomain hcode hleftState.
  destruct
    (raw_codedPALocalProofOf_dynamic_truth_sigma_or_fixed_production_of_four_roots
      M hPA translation sourceWitnessList sourceContext rowPrefix
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0
      modeRoot domainRoot codeRoot leftStateRoot
      hbase hmode hdomain hcode hleftState) as
    [fixedProductionRoot hfixed].
  exists fixedProductionRoot.
  rewrite <- hcodeIdentification.
  exact hfixed.
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaOrFixedProductionAppendIntegration.
