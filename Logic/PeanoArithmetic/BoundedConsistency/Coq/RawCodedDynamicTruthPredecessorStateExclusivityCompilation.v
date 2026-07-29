(**
  Compile predecessor-state exclusivity from the preceding local field.

  The implication/Boolean collision cells expose two synchronized earlier-
  state assumptions.  The preceding local field already proves that its
  admissible Sigma and Pi evidence cannot coexist.  The only genuinely
  table-specific work is therefore to turn the two state-member assumptions
  into the admissibility and evidence premises of one opened local-field
  instance.

  This module makes that reduction literal at represented-proof level.  It
  opens the carried triple-universal exclusivity law, transports it into the
  exact two-assumption context, performs three [Imp-E] steps, discharges both
  state assumptions, and restores the three universal binders.  No semantic
  soundness or model completeness is used.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedProofAtomicAdequacyStandard
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextShift
  RawCodedProofImpIConstructor
  RawCodedRestrictedPAProof
  RawCodedPAAxiomContextSelfShift
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPALocalProofWitnessedContextMergeTransportComplete
  RawCodedPALocalProofUniversalEliminationChain
  RawCodedPALocalProofTripleUniversalIntroduction
  RawCodedUniversalClosureDiagonalSubstitution
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateTripleUniversalOpening
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthNativeLocalPositiveGraph
  RawCodedDynamicTruthNativeLocalProofCompilation
  RawCodedDynamicTruthLocalExclusiveTemplateDirectInputs
  RawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation
  RawCodedDynamicTruthImpBranchExclusivity.

Module PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import
  PABoundedRawCodedPALocalProofWitnessedContextMergeTransportComplete.
Import PABoundedRawCodedPALocalProofUniversalEliminationChain.
Import PABoundedRawCodedPALocalProofTripleUniversalIntroduction.
Import PABoundedRawCodedUniversalClosureDiagonalSubstitution.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateTripleUniversalOpening.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthNativeLocalPositiveGraph.
Import PABoundedRawCodedDynamicTruthNativeLocalProofCompilation.
Import
  PABoundedRawCodedDynamicTruthLocalExclusiveTemplateDirectInputs.
Import
  PABoundedRawCodedDynamicTruthLocalExclusiveTemplateTraceCompilation.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.

(** The two open atoms and their implication body are named separately from
    the historical closed formula so later compilers can target their exact
    represented codes without destructing a quoted syntax tree. *)
Definition dynamicTruthPredecessorSigmaStateMemberBodyFormula : formula :=
  dynamicTruthStateMemberTermAt
    (tVar 15) (tVar 14) (tVar 13) (tVar 12)
    (tVar 11) (tVar 10) (tVar 9) (tVar 8)
    (tVar 7) (tVar 2) tZero (tVar 0)
    (tVar 4) (tVar 3).

Definition dynamicTruthPredecessorPiStateMemberBodyFormula : formula :=
  dynamicTruthStateMemberTermAt
    (tVar 15) (tVar 14) (tVar 13) (tVar 12)
    (tVar 11) (tVar 10) (tVar 9) (tVar 8)
    (tVar 7) (tVar 1) (Term.numeral 1) (tVar 0)
    (tVar 4) (tVar 3).

Definition dynamicTruthPredecessorStateExclusivityBodyFormula : formula :=
  pImp dynamicTruthPredecessorSigmaStateMemberBodyFormula
    (pImp dynamicTruthPredecessorPiStateMemberBodyFormula pBot).

Lemma dynamicTruthImpPredecessorStateExclusivityFormula_as_all3 :
  dynamicTruthImpPredecessorStateExclusivityFormula =
  pAll (pAll (pAll
    dynamicTruthPredecessorStateExclusivityBodyFormula)).
Proof.
  reflexivity.
Qed.

Definition rawDynamicTruthPredecessorSigmaStateMemberBodyCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    dynamicTruthPredecessorSigmaStateMemberBodyFormula.

Definition rawDynamicTruthPredecessorPiStateMemberBodyCode
    (M : RawPAModel) : M :=
  rawQuotedFormulaCode M
    dynamicTruthPredecessorPiStateMemberBodyFormula.

Definition rawDynamicTruthPredecessorStateExclusivityBodyCode
    (M : RawPAModel) : M :=
  rawFormulaImpCode M
    (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M)
    (rawFormulaImpCode M
      (rawDynamicTruthPredecessorPiStateMemberBodyCode M)
      (rawFormulaBotCode M)).

Arguments rawDynamicTruthPredecessorSigmaStateMemberBodyCode M
  : clear implicits.
Arguments rawDynamicTruthPredecessorPiStateMemberBodyCode M
  : clear implicits.
Arguments rawDynamicTruthPredecessorStateExclusivityBodyCode M
  : clear implicits.

Lemma rawDynamicTruthImpPredecessorStateExclusivityCode_as_all3 : forall
    (M : RawPAModel), RawPASatisfies M ->
  rawDynamicTruthImpPredecessorStateExclusivityCode M =
  rawFormulaAllCode M (rawFormulaAllCode M (rawFormulaAllCode M
    (rawDynamicTruthPredecessorStateExclusivityBodyCode M))).
Proof.
  intros M hPA.
  rewrite rawDynamicTruthImpPredecessorStateExclusivityCode_eq_quoted
    by exact hPA.
  rewrite dynamicTruthImpPredecessorStateExclusivityFormula_as_all3.
  unfold rawDynamicTruthPredecessorStateExclusivityBodyCode,
    dynamicTruthPredecessorStateExclusivityBodyFormula,
    rawDynamicTruthPredecessorSigmaStateMemberBodyCode,
    rawDynamicTruthPredecessorPiStateMemberBodyCode.
  reflexivity.
Qed.

Definition rawDynamicTruthPredecessorSigmaStateContext
    (M : RawPAModel) (baseContext : M) : M :=
  rawListNode M
    (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M) baseContext.

Definition rawDynamicTruthPredecessorJointStateContext
    (M : RawPAModel) (baseContext : M) : M :=
  rawListNode M
    (rawDynamicTruthPredecessorPiStateMemberBodyCode M)
    (rawDynamicTruthPredecessorSigmaStateContext M baseContext).

Arguments rawDynamicTruthPredecessorSigmaStateContext M baseContext
  : clear implicits.
Arguments rawDynamicTruthPredecessorJointStateContext M baseContext
  : clear implicits.

(** The three proof-producing leaves form one logical resource.  Keeping the
    package in [Prop] is deliberate: a trace compiler may obtain its carrier
    roots existentially and eliminate those existentials into this package,
    while Type-valued structural translations remain independent of the
    chosen proof-root witnesses. *)
Record RawDynamicTruthPredecessorStateLogicalRootsAt
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M) : Prop := {
  rawDynamicTruthPredecessorLogicalRoots_admissible : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) root;
  rawDynamicTruthPredecessorLogicalRoots_sigmaEvidence : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      sigmaEvidence root;
  rawDynamicTruthPredecessorLogicalRoots_piEvidence : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      piEvidence root
}.

Arguments RawDynamicTruthPredecessorStateLogicalRootsAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.

(** General proof-theoretic kernel.  The two assumptions need not be state
    atoms: any adequate formulas can be discharged.  Likewise the opened
    exclusive body can come from any verified elimination chain. *)
Theorem raw_codedPALocalProofOf_exclusive_bridge_close3 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context first second sigmaDomain piDomain
      sigmaEvidence piEvidence sourceRoot,
  RawContextListRealizable M context ->
  RawContextShift M context context ->
  RawCodedFormulaAtomicallyAdequate M first ->
  RawCodedFormulaAtomicallyAdequate M second ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    sourceRoot ->
  RawCodedUniversalEliminationChain M
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalExclusiveCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) ->
  (exists admissibleRoot,
    RawCodedPALocalProofOf M
      (rawListNode M second (rawListNode M first context))
      (rawDynamicTruthLocalAdmissibleCode M
        sigmaDomain piDomain) admissibleRoot) ->
  (exists sigmaRoot,
    RawCodedPALocalProofOf M
      (rawListNode M second (rawListNode M first context))
      sigmaEvidence sigmaRoot) ->
  (exists piRoot,
    RawCodedPALocalProofOf M
      (rawListNode M second (rawListNode M first context))
      piEvidence piRoot) ->
  exists resultRoot,
    RawCodedPALocalProofOf M context
      (rawFormulaAllCode M (rawFormulaAllCode M (rawFormulaAllCode M
        (rawFormulaImpCode M first
          (rawFormulaImpCode M second (rawFormulaBotCode M))))))
      resultRoot.
Proof.
  intros M hPA context first second sigmaDomain piDomain
    sigmaEvidence piEvidence sourceRoot hcontext hshift
    hfirstAdequate hsecondAdequate hsource
    hchain [admissibleRoot hadmissible]
    [sigmaRoot hsigma] [piRoot hpi].
  destruct (raw_codedPALocalProofOf_universal_elimination_chain
    M hPA context
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence))
    (rawDynamicTruthLocalExclusiveCode M
      sigmaDomain piDomain sigmaEvidence piEvidence)
    hchain sourceRoot hsource) as [openedRoot hopened].
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA context first
    (rawDynamicTruthLocalExclusiveCode M
      sigmaDomain piDomain sigmaEvidence piEvidence)
    openedRoot hfirstAdequate hcontext hopened)
    as [firstLiftedRoot hfirstLifted].
  assert (hfirstContext :
      RawContextListRealizable M (rawListNode M first context)).
  { exact (raw_contextList_cons_realizable M hPA context first hcontext). }
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA (rawListNode M first context) second
    (rawDynamicTruthLocalExclusiveCode M
      sigmaDomain piDomain sigmaEvidence piEvidence)
    firstLiftedRoot hsecondAdequate hfirstContext hfirstLifted)
    as [jointRoot hjoint].
  destruct (raw_codedPALocalProofOf_impE3 M hPA
    (rawListNode M second (rawListNode M first context))
    (rawDynamicTruthLocalAdmissibleCode M
      sigmaDomain piDomain)
    sigmaEvidence piEvidence (rawFormulaBotCode M)
    jointRoot admissibleRoot sigmaRoot piRoot
    hjoint hadmissible hsigma hpi) as [bottomRoot hbottom].
  pose proof (raw_codedPALocalProofOf_impI M hPA
    (rawListNode M first context) second (rawFormulaBotCode M)
    bottomRoot hbottom) as hsecondImp.
  pose proof (raw_codedPALocalProofOf_impI M hPA
    context first
    (rawFormulaImpCode M second (rawFormulaBotCode M))
    (rawProofImpIRoot M (rawListNode M first context)
      second (rawFormulaBotCode M) bottomRoot)
    hsecondImp) as hbody.
  exists (rawPALocalProofClose3Root M context
    (rawFormulaImpCode M first
      (rawFormulaImpCode M second (rawFormulaBotCode M)))
    (rawProofImpIRoot M context first
      (rawFormulaImpCode M second (rawFormulaBotCode M))
      (rawProofImpIRoot M (rawListNode M first context)
        second (rawFormulaBotCode M) bottomRoot))).
  exact (raw_codedPALocalProofOf_close3_on M hPA context
    (rawFormulaImpCode M first
      (rawFormulaImpCode M second (rawFormulaBotCode M)))
    (rawProofImpIRoot M context first
      (rawFormulaImpCode M second (rawFormulaBotCode M))
      (rawProofImpIRoot M (rawListNode M first context)
        second (rawFormulaBotCode M) bottomRoot))
    hshift hbody).
Qed.

(** Exact table/application residue for the predecessor specialization.  The
    record exposes the substitution chain and each of the three bridge roots
    independently, which lets later graph compilers discharge them as soon
    as their corresponding trace becomes available. *)
Record RawDynamicTruthPredecessorStateApplicationBridgeAt
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M) : Type := {
  rawDynamicTruthPredecessorBridge_elimination :
    RawCodedUniversalEliminationChain M
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalExclusiveCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence);
  rawDynamicTruthPredecessorBridge_admissible : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) root;
  rawDynamicTruthPredecessorBridge_sigmaEvidence : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      sigmaEvidence root;
  rawDynamicTruthPredecessorBridge_piEvidence : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      piEvidence root
}.

Arguments RawDynamicTruthPredecessorStateApplicationBridgeAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.

(** A smaller bridge presents diagonal self-instantiation of the exclusive
    body instead of spelling out the three [All-E] edges. *)
Record RawDynamicTruthPredecessorStateDiagonalApplicationBridgeAt
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M) : Type := {
  rawDynamicTruthPredecessorDiagonalBridge_stable :
    RawCodedFormulaDiagonalSubstitutionAtAllDepths M
      (rawQuotedTermCode M (tVar 0))
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence);
  rawDynamicTruthPredecessorDiagonalBridge_admissible : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) root;
  rawDynamicTruthPredecessorDiagonalBridge_sigmaEvidence : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      sigmaEvidence root;
  rawDynamicTruthPredecessorDiagonalBridge_piEvidence : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      piEvidence root
}.

Arguments RawDynamicTruthPredecessorStateDiagonalApplicationBridgeAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.

(** The natural three-variable bridge is structural rather than diagonal.
    Its template body may contain opaque applications translating to
    nonstandard formula codes; the translation's opening law tracks their
    two shifted intermediate instances.  A finite scope proof then recovers
    the original body after the exact [#2], [#1], [#0] elimination sequence. *)
Record RawDynamicTruthPredecessorStateTemplateApplicationBridgeAt
    (M : RawPAModel)
    (baseContext sigmaDomain piDomain sigmaEvidence piEvidence : M) : Type := {
  rawDynamicTruthPredecessorTemplateBridge_translation :
    RawCodedTemplateTranslation M;
  rawDynamicTruthPredecessorTemplateBridge_body : TemplateFormula;
  rawDynamicTruthPredecessorTemplateBridge_scoped :
    TemplateFormulaScoped 3
      rawDynamicTruthPredecessorTemplateBridge_body;
  rawDynamicTruthPredecessorTemplateBridge_bodyCode :
    rawTemplateFormula rawDynamicTruthPredecessorTemplateBridge_translation
      rawDynamicTruthPredecessorTemplateBridge_body =
    rawDynamicTruthLocalExclusiveCode M
      sigmaDomain piDomain sigmaEvidence piEvidence;
  rawDynamicTruthPredecessorTemplateBridge_admissible : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) root;
  rawDynamicTruthPredecessorTemplateBridge_sigmaEvidence : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      sigmaEvidence root;
  rawDynamicTruthPredecessorTemplateBridge_piEvidence : exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      piEvidence root
}.

Arguments RawDynamicTruthPredecessorStateTemplateApplicationBridgeAt
  M baseContext sigmaDomain piDomain sigmaEvidence piEvidence
  : clear implicits.

(** Direct structural identification discharges every syntactic coordinate
    of the template bridge.  Downstream table compilers now need to supply
    only the three genuinely logical roots in the joint predecessor-state
    context; selector choice, scoping, and the exact body-code equation are
    reconstructed here. *)
Theorem
    raw_dynamicTruthPredecessorStateTemplateApplicationBridgeAt_of_direct :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  (exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) root) ->
  (exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      sigmaEvidence root) ->
  (exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      piEvidence root) ->
  RawDynamicTruthPredecessorStateTemplateApplicationBridgeAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    inputs hidentification hadmissible hsigma hpi.
  refine
    {| rawDynamicTruthPredecessorTemplateBridge_translation :=
         rawDirectStructuralTemplateTranslation M hPA inputs;
       rawDynamicTruthPredecessorTemplateBridge_body :=
         coqDynamicTruthLocalExclusiveBodyTemplate;
       rawDynamicTruthPredecessorTemplateBridge_scoped :=
         coqDynamicTruthLocalExclusiveBodyTemplate_scoped;
       rawDynamicTruthPredecessorTemplateBridge_bodyCode := _;
       rawDynamicTruthPredecessorTemplateBridge_admissible := hadmissible;
       rawDynamicTruthPredecessorTemplateBridge_sigmaEvidence := hsigma;
       rawDynamicTruthPredecessorTemplateBridge_piEvidence := hpi |}.
  change
    (rawDirectTemplateFormula inputs
      coqDynamicTruthLocalExclusiveBodyTemplate =
     rawDynamicTruthLocalExclusiveCode M
       sigmaDomain piDomain sigmaEvidence piEvidence).
  exact (rawCoqDynamicTruthLocalExclusiveBodyTemplate_identified
    M hPA inputs sigmaDomain piDomain sigmaEvidence piEvidence
    hidentification).
Qed.

(** Package-based form of the direct structural bridge.  Its conclusion is
    Type-valued, but it only projects Prop-valued fields; it never chooses or
    inspects the existential carrier roots. *)
Corollary
    raw_dynamicTruthPredecessorStateTemplateApplicationBridgeAt_of_direct_logical_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  RawCoqDynamicTruthLocalExclusiveTemplateIdentification M inputs
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawDynamicTruthPredecessorStateLogicalRootsAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawDynamicTruthPredecessorStateTemplateApplicationBridgeAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    inputs hidentification hroots.
  exact
    (raw_dynamicTruthPredecessorStateTemplateApplicationBridgeAt_of_direct
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      inputs hidentification
      (rawDynamicTruthPredecessorLogicalRoots_admissible
        M baseContext sigmaDomain piDomain sigmaEvidence piEvidence hroots)
      (rawDynamicTruthPredecessorLogicalRoots_sigmaEvidence
        M baseContext sigmaDomain piDomain sigmaEvidence piEvidence hroots)
      (rawDynamicTruthPredecessorLogicalRoots_piEvidence
        M baseContext sigmaDomain piDomain sigmaEvidence piEvidence hroots)).
Qed.

Theorem raw_dynamicTruthPredecessorStateApplicationBridgeAt_of_diagonal :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthPredecessorStateDiagonalApplicationBridgeAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawDynamicTruthPredecessorStateApplicationBridgeAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    [hstable hadmissible hsigma hpi].
  refine
    {| rawDynamicTruthPredecessorBridge_elimination := _;
       rawDynamicTruthPredecessorBridge_admissible := hadmissible;
       rawDynamicTruthPredecessorBridge_sigmaEvidence := hsigma;
       rawDynamicTruthPredecessorBridge_piEvidence := hpi |}.
  unfold rawDynamicTruthLocalFormulaAll3Code.
  exact (raw_codedUniversalEliminationChain_all3_of_diagonal
    M hPA (rawQuotedTermCode M (tVar 0))
    (rawDynamicTruthLocalExclusiveCode M
      sigmaDomain piDomain sigmaEvidence piEvidence) hstable).
Qed.

(** Convert the honest translated-template presentation to the historical
    chain-level interface.  Unlike the diagonal adapter, this theorem does
    not require either intermediate All-E result to equal its source. *)
Theorem raw_dynamicTruthPredecessorStateApplicationBridgeAt_of_template :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence,
  RawDynamicTruthPredecessorStateTemplateApplicationBridgeAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  RawDynamicTruthPredecessorStateApplicationBridgeAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence.
Proof.
  intros M _ baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    [translation body hscoped hbody
      hadmissible hsigmaEvidence hpiEvidence].
  refine
    {| rawDynamicTruthPredecessorBridge_elimination := _;
       rawDynamicTruthPredecessorBridge_admissible := hadmissible;
       rawDynamicTruthPredecessorBridge_sigmaEvidence := hsigmaEvidence;
       rawDynamicTruthPredecessorBridge_piEvidence := hpiEvidence |}.
  pose proof (raw_template_all3_variables_elimination_chain
    M translation body hscoped) as hchain.
  rewrite !rawTemplateFormula_all in hchain.
  rewrite hbody in hchain.
  exact hchain.
Qed.

Theorem raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) sourceRoot ->
  RawDynamicTruthPredecessorStateApplicationBridgeAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists predecessorRoot,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sourceRoot hcontext hshift hsource
    [hchain hadmissible hsigma hpi].
  destruct (raw_codedPALocalProofOf_exclusive_bridge_close3 M hPA
    baseContext
    (rawDynamicTruthPredecessorSigmaStateMemberBodyCode M)
    (rawDynamicTruthPredecessorPiStateMemberBodyCode M)
    sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
    hcontext hshift
    (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorSigmaStateMemberBodyFormula)
    (raw_quotedFormula_atomically_adequate M hPA
      dynamicTruthPredecessorPiStateMemberBodyFormula)
    hsource hchain hadmissible hsigma hpi) as [root hroot].
  exists root.
  rewrite rawDynamicTruthImpPredecessorStateExclusivityCode_as_all3
    by exact hPA.
  exact hroot.
Qed.

Corollary
    raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive_diagonal :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) sourceRoot ->
  RawDynamicTruthPredecessorStateDiagonalApplicationBridgeAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists predecessorRoot,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sourceRoot hcontext hshift hsource hbridge.
  exact
    (raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      sourceRoot hcontext hshift hsource
      (raw_dynamicTruthPredecessorStateApplicationBridgeAt_of_diagonal
        M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
        hbridge)).
Qed.

Corollary
    raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive_template :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) sourceRoot ->
  RawDynamicTruthPredecessorStateTemplateApplicationBridgeAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists predecessorRoot,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
    sourceRoot hcontext hshift hsource hbridge.
  exact
    (raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      sourceRoot hcontext hshift hsource
      (raw_dynamicTruthPredecessorStateApplicationBridgeAt_of_template
        M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
        hbridge)).
Qed.

(** Context-growing form of the template closure.  The carried exclusivity
    proof may have been compiled before a later traversal added PA witnesses.
    It therefore lives in an arbitrary realizable source context.  A witnessed
    target context containing that source is enough to transport the proof,
    and also supplies the realizability and self-shift facts needed to close
    the two predecessor-state assumptions there.

    Notice that no witness package or self-shift is required for the source
    context.  This is the weakest interface exposed by the completed
    binder-safe weakening theorem and is useful for all growing compilers,
    not just the native-trace corollary below. *)
Theorem
    raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive_template_on_witnessed_extension :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      sourceContext targetWitnessList targetContext
      sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawContextListRealizable M sourceContext ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M sourceContext targetContext ->
  RawCodedPALocalProofOf M sourceContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) sourceRoot ->
  RawDynamicTruthPredecessorStateTemplateApplicationBridgeAt M targetContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists predecessorRoot,
    RawCodedPALocalProofOf M targetContext
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA sourceContext targetWitnessList targetContext
    sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
    hsourceContext htargetWitnessed hincluded hsource hbridge.
  assert (htargetContext : RawContextListRealizable M targetContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable M
      targetWitnessList targetContext htargetWitnessed).
  }
  destruct
    (raw_codedPALocalProof_contextInclusionWeakening_of_binderReady
      M hPA sourceContext targetContext
      (rawDynamicTruthLocalFormulaAll3Code M
        (rawDynamicTruthLocalExclusiveCode M
          sigmaDomain piDomain sigmaEvidence piEvidence))
      sourceRoot hsourceContext htargetContext hincluded
      (raw_contextBinderReady_witnessed_target M hPA
        sourceContext targetContext targetWitnessList
        hincluded htargetWitnessed)
      hsource) as [transportedRoot htransported].
  exact
    (raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive_template
      M hPA targetContext sigmaDomain piDomain sigmaEvidence piEvidence
      transportedRoot htargetContext
      (raw_codedPAAxiomWitnessContext_selfShift M hPA
        targetWitnessList targetContext htargetWitnessed)
      htransported hbridge).
Qed.

(** Native traces can be eliminated safely here because the final result is
    a proposition.  This avoids any forbidden large elimination from the
    trace's existentially selected [Type]-valued translation witness while
    still leaving only the three logical roots as premises. *)
Corollary
    raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_native_trace :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) sourceRoot ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  (exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      (rawDynamicTruthLocalAdmissibleCode M sigmaDomain piDomain) root) ->
  (exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      sigmaEvidence root) ->
  (exists root,
    RawCodedPALocalProofOf M
      (rawDynamicTruthPredecessorJointStateContext M baseContext)
      piEvidence root) ->
  exists predecessorRoot,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
    hcontext hshift hsource htrace hadmissible hsigma hpi.
  destruct
    (raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_native_trace
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    [inputs hidentification].
  apply
    (raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive_template
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      sourceRoot hcontext hshift hsource).
  exact
    (raw_dynamicTruthPredecessorStateTemplateApplicationBridgeAt_of_direct
      M hPA baseContext sigmaDomain piDomain sigmaEvidence piEvidence
      inputs hidentification hadmissible hsigma hpi).
Qed.

(** The package form is the natural Prop-valued endpoint for callers which
    construct the three leaves together under the joint state context. *)
Corollary
    raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_native_trace_logical_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawContextListRealizable M baseContext ->
  RawContextShift M baseContext baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) sourceRoot ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthPredecessorStateLogicalRootsAt M baseContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists predecessorRoot,
    RawCodedPALocalProofOf M baseContext
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    baseContext sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
    hcontext hshift hsource htrace hroots.
  exact
    (raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_native_trace
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      baseContext sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
      hcontext hshift hsource htrace
      (rawDynamicTruthPredecessorLogicalRoots_admissible
        M baseContext sigmaDomain piDomain sigmaEvidence piEvidence hroots)
      (rawDynamicTruthPredecessorLogicalRoots_sigmaEvidence
        M baseContext sigmaDomain piDomain sigmaEvidence piEvidence hroots)
      (rawDynamicTruthPredecessorLogicalRoots_piEvidence
        M baseContext sigmaDomain piDomain sigmaEvidence piEvidence hroots)).
Qed.

(** Native-trace endpoint matching the output shape of growing global-
    traversal compilers.  The local exclusivity proof is transported from its
    earlier context, while the three logical roots are consumed directly in
    the common witnessed extension where the traversal produced them. *)
Corollary
    raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_native_trace_on_witnessed_extension_logical_roots :
    forall (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) predecessorLevel inputGlobalSigma inputGlobalPi
      sourceContext targetWitnessList targetContext
      sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot,
  RawContextListRealizable M sourceContext ->
  RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
  RawContextListIncluded M sourceContext targetContext ->
  RawCodedPALocalProofOf M sourceContext
    (rawDynamicTruthLocalFormulaAll3Code M
      (rawDynamicTruthLocalExclusiveCode M
        sigmaDomain piDomain sigmaEvidence piEvidence)) sourceRoot ->
  RawDynamicTruthNativeLocalProofTraceAt M tail predecessorLevel
    inputGlobalSigma inputGlobalPi sigmaDomain piDomain
    sigmaEvidence piEvidence ->
  RawDynamicTruthPredecessorStateLogicalRootsAt M targetContext
    sigmaDomain piDomain sigmaEvidence piEvidence ->
  exists predecessorRoot,
    RawCodedPALocalProofOf M targetContext
      (rawDynamicTruthImpPredecessorStateExclusivityCode M)
      predecessorRoot.
Proof.
  intros M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
    sourceContext targetWitnessList targetContext
    sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
    hsourceContext htargetWitnessed hincluded hsource htrace hroots.
  destruct
    (raw_coqDynamicTruthLocalExclusiveTemplateIdentification_of_native_trace
      M hPA tail predecessorLevel inputGlobalSigma inputGlobalPi
      sigmaDomain piDomain sigmaEvidence piEvidence htrace) as
    [inputs hidentification].
  apply
    (raw_dynamicTruthImpPredecessorStateExclusivityRoot_of_local_exclusive_template_on_witnessed_extension
      M hPA sourceContext targetWitnessList targetContext
      sigmaDomain piDomain sigmaEvidence piEvidence sourceRoot
      hsourceContext htargetWitnessed hincluded hsource).
  exact
    (raw_dynamicTruthPredecessorStateTemplateApplicationBridgeAt_of_direct_logical_roots
      M hPA targetContext sigmaDomain piDomain sigmaEvidence piEvidence
      inputs hidentification hroots).
Qed.

End PABoundedRawCodedDynamicTruthPredecessorStateExclusivityCompilation.
