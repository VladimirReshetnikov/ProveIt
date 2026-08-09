(**
  Synchronize the three residual guarded canonical Sigma/Or leaves.

  The guarded canonical consumer deliberately exposes three proof-producing
  leaves: the instantiated Sigma domain, the parent Or-code atom, and the
  selected left-state atom.  They are not the append extension's four lookup
  projections, and none is a theorem in an arbitrary caller prefix.  A
  correct producer must therefore continue to expose a represented compiler
  for each leaf (or refute the temporary context).

  Requiring all three producers to choose one standard PA-witness extension
  at once is nevertheless unnecessary.  This module factors a reusable
  single-formula compiler, permits each leaf to grow the witnessed tail
  independently, and invokes the producers in dependency order.  Earlier
  roots are transported under the unchanged thirteen-binder prefix after
  each later extension.  The final meta-level witness prefix is the literal
  concatenation of the three selected batches.

  The refutation alternative is retained at every leaf.  Represented bottom
  elimination converts it to the requested leaf in the same context, so the
  public fixed-production theorem consumes a strictly weaker interface than
  the simultaneous three-root callback it feeds.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate
  RawCodedDynamicTruthSigmaOrGuardedCanonicalTranslationSynchronization
  RawCodedDynamicTruthSigmaOrGuardedCanonicalConsumerIntegration.

Module
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalThreeRootCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.
Import
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalTranslationSynchronization.
Import
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalConsumerIntegration.

(** A standard-witness growing compiler for one literal template formula.
    Unlike the more general carrier-level growing package, its output tail
    remains definitionally a finite meta-level PA-axiom witness prefix.  That
    stronger shape is exactly what lets three dependency-ordered extensions
    be concatenated into the historical consumer's output type. *)
Definition RawCodedPAStandardWitnessGrowingTemplateFormulaCompilerAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (prefix : TemplateContext) (formula : TemplateFormula) : Prop :=
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        prefix)
      (rawTemplateFormula translation formula) root.

Arguments RawCodedPAStandardWitnessGrowingTemplateFormulaCompilerAt
  M translation prefix formula : clear implicits.

(** A contradictory temporary context is an honest substitute for a leaf
    proof.  The same root is used by either disjunct, matching the existing
    canonical fixed-production-or-refutation interfaces. *)
Definition
    RawCodedPAStandardWitnessGrowingTemplateFormulaOrRefutationCompilerAt
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (prefix : TemplateContext) (formula : TemplateFormula) : Prop :=
  forall sourceWitnessList sourceContext,
  RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses sourceContext) /\
    (RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        prefix)
      (rawTemplateFormula translation formula) root \/
     RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses sourceContext)
        prefix)
      (rawFormulaBotCode M) root).

Arguments
  RawCodedPAStandardWitnessGrowingTemplateFormulaOrRefutationCompilerAt
  M translation prefix formula : clear implicits.

(** Bottom elimination normalizes the relaxed compiler without changing its
    chosen witnesses or temporary context. *)
Theorem
    raw_codedPAStandardWitnessGrowingTemplateFormulaCompilerAt_of_or_refutation :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M) prefix formula,
  RawCodedPAStandardWitnessGrowingTemplateFormulaOrRefutationCompilerAt
    M translation prefix formula ->
  RawCodedPAStandardWitnessGrowingTemplateFormulaCompilerAt
    M translation prefix formula.
Proof.
  intros M hPA translation prefix formula hcompiler
    sourceWitnessList sourceContext hsource.
  destruct (hcompiler sourceWitnessList sourceContext hsource) as
    (witnesses & root & htarget & [hformula | hbottom]).
  - exists witnesses, root. split; assumption.
  - exists witnesses. eexists.
    split; [exact htarget |].
    exact (raw_codedPALocalProofOf_botE M hPA _ root hbottom _).
Qed.

(** Name the three exact formulas.  These aliases are intentionally
    transparent: their bodies are the literal witnesses selected by the
    downstream finite Sigma/Or proof, not a semantic approximation. *)
Definition coqDynamicTruthSigmaOrGuardedCanonicalDomainRootTemplate
    : TemplateFormula :=
  coqDynamicTruthSigmaOrOpenedDomainAt
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0).

Definition coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate
    : TemplateFormula :=
  coqDynamicTruthSigmaOrOpenedCodeAt
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0).

Definition coqDynamicTruthSigmaOrGuardedCanonicalLeftStateRootTemplate
    : TemplateFormula :=
  coqDynamicTruthSigmaOrOpenedLeftStateAt
    (ttVar 7) (ttVar 6) (ttVar 5) (ttVar 4)
    (ttVar 3) (ttVar 2) (ttVar 1) (ttVar 0).

(** The exact residual, split into independently growing components.  A
    record makes it impossible to accidentally exchange the parent-code and
    selected-state leaves merely because their compiler shapes coincide. *)
Record
    RawDynamicTruthSigmaOrGuardedCanonicalIndependentGrowingThreeRootCompilersUnderPrefixAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (outerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthSigmaOrGuardedCanonical_domainCompiler :
    RawCodedPAStandardWitnessGrowingTemplateFormulaCompilerAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
      coqDynamicTruthSigmaOrGuardedCanonicalDomainRootTemplate;
  rawDynamicTruthSigmaOrGuardedCanonical_codeCompiler :
    RawCodedPAStandardWitnessGrowingTemplateFormulaCompilerAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
      coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate;
  rawDynamicTruthSigmaOrGuardedCanonical_leftStateCompiler :
    RawCodedPAStandardWitnessGrowingTemplateFormulaCompilerAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
      coqDynamicTruthSigmaOrGuardedCanonicalLeftStateRootTemplate
}.

Arguments
  RawDynamicTruthSigmaOrGuardedCanonicalIndependentGrowingThreeRootCompilersUnderPrefixAt
  M hPA inputs outerPrefix : clear implicits.

(** Relax every component independently by permitting a represented
    refutation of the same temporary context. *)
Record
    RawDynamicTruthSigmaOrGuardedCanonicalIndependentGrowingThreeRootOrRefutationCompilersUnderPrefixAt
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    (outerPrefix : TemplateContext) : Prop := {
  rawDynamicTruthSigmaOrGuardedCanonical_domainOrRefutationCompiler :
    RawCodedPAStandardWitnessGrowingTemplateFormulaOrRefutationCompilerAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
      coqDynamicTruthSigmaOrGuardedCanonicalDomainRootTemplate;
  rawDynamicTruthSigmaOrGuardedCanonical_codeOrRefutationCompiler :
    RawCodedPAStandardWitnessGrowingTemplateFormulaOrRefutationCompilerAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
      coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate;
  rawDynamicTruthSigmaOrGuardedCanonical_leftStateOrRefutationCompiler :
    RawCodedPAStandardWitnessGrowingTemplateFormulaOrRefutationCompilerAt M
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      (coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix)
      coqDynamicTruthSigmaOrGuardedCanonicalLeftStateRootTemplate
}.

Arguments
  RawDynamicTruthSigmaOrGuardedCanonicalIndependentGrowingThreeRootOrRefutationCompilersUnderPrefixAt
  M hPA inputs outerPrefix : clear implicits.

Theorem
    raw_dynamicTruthSigmaOrGuardedCanonical_independentGrowingThreeRootCompilersUnderPrefixAt_of_or_refutation :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) outerPrefix,
  RawDynamicTruthSigmaOrGuardedCanonicalIndependentGrowingThreeRootOrRefutationCompilersUnderPrefixAt
    M hPA inputs outerPrefix ->
  RawDynamicTruthSigmaOrGuardedCanonicalIndependentGrowingThreeRootCompilersUnderPrefixAt
    M hPA inputs outerPrefix.
Proof.
  intros M hPA inputs outerPrefix
    [hdomain hcode hleftState].
  constructor;
    apply
      raw_codedPAStandardWitnessGrowingTemplateFormulaCompilerAt_of_or_refutation;
    assumption.
Qed.

(** Dependency-ordered synchronization.  The code producer runs after the
    domain producer and the selected-state producer runs after both.  This
    avoids a carrier-level merge and retains a literal standard witness
    prefix, while the two transports below preserve the complete temporary
    template prefix. *)
Theorem
    raw_dynamicTruthSigmaOrGuardedCanonical_growingThreeRootCompilerUnderPrefixAt_of_independent :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) outerPrefix,
  RawDynamicTruthSigmaOrGuardedCanonicalIndependentGrowingThreeRootCompilersUnderPrefixAt
    M hPA inputs outerPrefix ->
  RawDynamicTruthSigmaOrGuardedCanonicalGrowingThreeRootCompilerUnderPrefixAt
    M hPA inputs outerPrefix.
Proof.
  intros M hPA inputs outerPrefix
    [hdomainCompiler hcodeCompiler hleftStateCompiler]
    sourceWitnessList sourceContext hsource.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  set (prefix :=
    coqDynamicTruthSigmaOrGuardedCanonicalModeZeroRowPrefix outerPrefix).

  destruct (hdomainCompiler sourceWitnessList sourceContext hsource) as
    (domainWitnesses & domainRoot & hdomainWitnessed & hdomain).
  destruct (hcodeCompiler
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        domainWitnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        domainWitnesses sourceContext)
      hdomainWitnessed) as
    (codeWitnesses & codeRoot & hcodeWitnessed & hcode).

  assert (hdomainCodeIncluded : RawContextListIncluded M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        domainWitnesses sourceContext)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          domainWitnesses sourceContext))).
  {
    exact
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA codeWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          domainWitnesses sourceContext)).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        domainWitnesses sourceWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        domainWitnesses sourceContext)
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          domainWitnesses sourceWitnessList))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          domainWitnesses sourceContext))
      prefix
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrGuardedCanonicalDomainRootTemplate)
      domainRoot hdomainWitnessed hcodeWitnessed hdomainCodeIncluded
      hdomain) as [domainCodeRoot hdomainCode].

  destruct (hleftStateCompiler
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          domainWitnesses sourceWitnessList))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          domainWitnesses sourceContext))
      hcodeWitnessed) as
    (leftStateWitnesses & leftStateRoot & hleftStateWitnessed & hleftState).

  assert (hcodeLeftStateIncluded : RawContextListIncluded M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          domainWitnesses sourceContext))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        leftStateWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          codeWitnesses
          (rawStandardPAAxiomWitnessPrefixContextCode M
            domainWitnesses sourceContext)))).
  {
    exact
      (raw_standardPAAxiomWitnessPrefixContextCode_target_included
        M hPA leftStateWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          codeWitnesses
          (rawStandardPAAxiomWitnessPrefixContextCode M
            domainWitnesses sourceContext))).
  }
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          domainWitnesses sourceWitnessList))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          domainWitnesses sourceContext))
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        leftStateWitnesses
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          codeWitnesses
          (rawStandardPAAxiomWitnessPrefixWitnessListCode M
            domainWitnesses sourceWitnessList)))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        leftStateWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          codeWitnesses
          (rawStandardPAAxiomWitnessPrefixContextCode M
            domainWitnesses sourceContext)))
      prefix
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrGuardedCanonicalDomainRootTemplate)
      domainCodeRoot hcodeWitnessed hleftStateWitnessed
      hcodeLeftStateIncluded hdomainCode) as
    [finalDomainRoot hfinalDomain].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          domainWitnesses sourceWitnessList))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        codeWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          domainWitnesses sourceContext))
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        leftStateWitnesses
        (rawStandardPAAxiomWitnessPrefixWitnessListCode M
          codeWitnesses
          (rawStandardPAAxiomWitnessPrefixWitnessListCode M
            domainWitnesses sourceWitnessList)))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        leftStateWitnesses
        (rawStandardPAAxiomWitnessPrefixContextCode M
          codeWitnesses
          (rawStandardPAAxiomWitnessPrefixContextCode M
            domainWitnesses sourceContext)))
      prefix
      (rawTemplateFormula translation
        coqDynamicTruthSigmaOrGuardedCanonicalCodeRootTemplate)
      codeRoot hcodeWitnessed hleftStateWitnessed
      hcodeLeftStateIncluded hcode) as
    [finalCodeRoot hfinalCode].

  exists (leftStateWitnesses ++ (codeWitnesses ++ domainWitnesses)),
    finalDomainRoot, finalCodeRoot, leftStateRoot.
  rewrite !rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
  rewrite !rawStandardPAAxiomWitnessPrefixContextCode_app.
  split; [exact hleftStateWitnessed |].
  split.
  - unfold translation, prefix in hfinalDomain |- *.
    exact hfinalDomain.
  - split.
    + unfold translation, prefix in hfinalCode |- *.
      exact hfinalCode.
    + unfold translation, prefix in hleftState |- *.
      exact hleftState.
Qed.

(** Public relaxed endpoint: three independently growing leaf-or-bottom
    compilers suffice for the literal guarded canonical fixed production. *)
Theorem
    raw_dynamicTruthSigmaOrGuardedCanonical_growingFixedProductionCompilerUnderPrefixAt_of_independent_three_roots_or_refutations :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) outerPrefix,
  RawDynamicTruthSigmaOrGuardedCanonicalTranslationIdentification
    M inputs ->
  RawDynamicTruthSigmaOrGuardedCanonicalIndependentGrowingThreeRootOrRefutationCompilersUnderPrefixAt
    M hPA inputs outerPrefix ->
  RawDynamicTruthSigmaOrGuardedCanonicalGrowingFixedProductionConsumerUnderPrefixAt
    M hPA inputs outerPrefix.
Proof.
  intros M hPA inputs outerPrefix hidentification hcompilers.
  apply
    (raw_dynamicTruthSigmaOrGuardedCanonical_growingFixedProductionCompilerUnderPrefixAt_of_three_roots
      M hPA inputs outerPrefix hidentification).
  apply
    raw_dynamicTruthSigmaOrGuardedCanonical_growingThreeRootCompilerUnderPrefixAt_of_independent.
  exact
    (raw_dynamicTruthSigmaOrGuardedCanonical_independentGrowingThreeRootCompilersUnderPrefixAt_of_or_refutation
      M hPA inputs outerPrefix hcompilers).
Qed.

End
  PABoundedRawCodedDynamicTruthSigmaOrGuardedCanonicalThreeRootCompilation.
