(**
  Coverage-certified compilation of proof templates over an arbitrary
  carrier-coded context tail.

  The original template compiler folds every finite template context onto
  [raw_zero].  Staged PA constructions instead work above an already
  witnessed PA-axiom context, which may be nonstandard.  This module keeps
  the finite metatheoretic template prefix but folds it over a supplied raw
  tail.  No formula or context code is decoded.

  Universal introduction and existential elimination shift their ambient
  context.  The finite prefix is shifted pointwise by the template
  translation, while the tail is reused through the explicit hypothesis
  [RawContextShift M baseTail baseTail].
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedContextLists RawCodedContextStructure RawCodedContextShift
  RawCodedProofEndpoints RawCodedProofRuleCoverage
  RawCodedProofAssumptionLeaf RawCodedProofImpIConstructor
  RawCodedProofBinaryConstructors RawCodedProofUnaryConstructors
  RawCodedProofLeafConstructors RawCodedProofAndIConstructor
  RawCodedProofAndEConstructors RawCodedProofOrIConstructors
  RawCodedProofOrEConstructor RawCodedProofAllIConstructor
  RawCodedProofAllEConstructor RawCodedProofExIConstructor
  RawCodedProofExEConstructor RawCodedProofEqReflConstructor
  RawCodedProofEqElimConstructor RawCodedPALocalProofExistential
  RawCodedTemplateProofCompiler RawCodedRestrictedPAProof
  RawCodedPAProofImpICertificates
  RawCodedPAAxiomContextSelfShift.

Import ListNotations.

Module PABoundedRawCodedTemplateProofCompilerSelfShiftTail.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofLeafConstructors.
Import PABoundedRawCodedProofAndIConstructor.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedProofOrIConstructors.
Import PABoundedRawCodedProofOrEConstructor.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedProofExIConstructor.
Import PABoundedRawCodedProofExEConstructor.
Import PABoundedRawCodedProofEqReflConstructor.
Import PABoundedRawCodedProofEqElimConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProofImpICertificates.
Import PABoundedRawCodedPAAxiomContextSelfShift.

(** Fold a finite translated template prefix over an arbitrary raw context
    tail.  The prefix order is identical to [rawTemplateContextCode]. *)
Fixpoint rawTemplateContextCodeOnTail {M : RawPAModel}
    (translation : RawCodedTemplateTranslation M)
    (baseTail : M) (context : TemplateContext) : M :=
  match context with
  | [] => baseTail
  | formula :: contextTail =>
      rawListNode M (rawTemplateFormula translation formula)
        (rawTemplateContextCodeOnTail translation baseTail contextTail)
  end.

Arguments rawTemplateContextCodeOnTail {M} translation baseTail context.

(** Each proof node is assembled from already translated rule fields. *)
Fixpoint rawTemplateProofCodeOnTail {M : RawPAModel}
    (translation : RawCodedTemplateTranslation M)
    (baseTail : M) (derivation : TemplateRawProof) : M :=
  match derivation with
  | trpAss context formula =>
      rawProofAssumptionRoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation formula)
  | trpImpI context antecedent consequent child =>
      rawProofImpIRoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation antecedent)
        (rawTemplateFormula translation consequent)
        (rawTemplateProofCodeOnTail translation baseTail child)
  | trpImpE context antecedent consequent implicationChild antecedentChild =>
      rawProofImpERoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation antecedent)
        (rawTemplateFormula translation consequent)
        (rawTemplateProofCodeOnTail translation baseTail implicationChild)
        (rawTemplateProofCodeOnTail translation baseTail antecedentChild)
  | trpBotE context conclusion child =>
      rawProofBotERoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation conclusion)
        (rawTemplateProofCodeOnTail translation baseTail child)
  | trpLem context body =>
      rawProofLemRoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation body)
  | trpAndI context leftFormula rightFormula leftChild rightChild =>
      rawProofAndIRoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCodeOnTail translation baseTail leftChild)
        (rawTemplateProofCodeOnTail translation baseTail rightChild)
  | trpAndE1 context leftFormula rightFormula child =>
      rawProofAndERoot M RawAndLeft
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCodeOnTail translation baseTail child)
  | trpAndE2 context leftFormula rightFormula child =>
      rawProofAndERoot M RawAndRight
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCodeOnTail translation baseTail child)
  | trpOrI1 context leftFormula rightFormula child =>
      rawProofOrIRoot M RawOrLeft
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCodeOnTail translation baseTail child)
  | trpOrI2 context leftFormula rightFormula child =>
      rawProofOrIRoot M RawOrRight
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCodeOnTail translation baseTail child)
  | trpOrE context leftFormula rightFormula conclusion disjunctionChild
      leftChild rightChild =>
      rawProofOrERoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateFormula translation conclusion)
        (rawTemplateProofCodeOnTail translation baseTail disjunctionChild)
        (rawTemplateProofCodeOnTail translation baseTail leftChild)
        (rawTemplateProofCodeOnTail translation baseTail rightChild)
  | trpAllI context body child =>
      rawProofAllIRoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation body)
        (rawTemplateProofCodeOnTail translation baseTail child)
  | trpAllE context body replacement child =>
      rawProofAllERoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation body)
        (rawTemplateTerm translation replacement)
        (rawTemplateProofCodeOnTail translation baseTail child)
  | trpExI context body replacement child =>
      rawProofExIRoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation body)
        (rawTemplateTerm translation replacement)
        (rawTemplateProofCodeOnTail translation baseTail child)
  | trpExE context body conclusion existentialChild bodyChild =>
      rawProofExERoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateFormula translation body)
        (rawTemplateFormula translation conclusion)
        (rawTemplateProofCodeOnTail translation baseTail existentialChild)
        (rawTemplateProofCodeOnTail translation baseTail bodyChild)
  | trpEqRefl context witness =>
      rawProofEqReflRoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateTerm translation witness)
  | trpEqElim context source target motive equalityChild motiveChild =>
      rawProofEqElimRoot M
        (rawTemplateContextCodeOnTail translation baseTail context)
        (rawTemplateTerm translation source)
        (rawTemplateTerm translation target)
        (rawTemplateFormula translation motive)
        (rawTemplateProofCodeOnTail translation baseTail equalityChild)
        (rawTemplateProofCodeOnTail translation baseTail motiveChild)
  end.

Arguments rawTemplateProofCodeOnTail {M} translation baseTail derivation.

(** ------------------------------------------------------------------
    Structural context facts above the supplied tail. *)

Lemma raw_templateContextOnTail_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      translation baseTail context,
  RawContextListRealizable M baseTail ->
  RawContextListRealizable M
    (rawTemplateContextCodeOnTail translation baseTail context).
Proof.
  intros M hPA translation baseTail context htail.
  induction context as [|formula contextTail ih]; cbn.
  - exact htail.
  - exact (raw_contextList_cons_realizable M hPA _ _ ih).
Qed.

Lemma raw_templateContextOnTail_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      translation baseTail context formula,
  RawContextListRealizable M baseTail ->
  In formula context ->
  RawContextListMember M
    (rawTemplateContextCodeOnTail translation baseTail context)
    (rawTemplateFormula translation formula).
Proof.
  intros M hPA translation baseTail context.
  induction context as [|head contextTail ih];
    intros formula htail hin; cbn in hin |- *.
  - contradiction.
  - destruct hin as [-> | hin].
    + apply raw_contextList_cons_head_member; [exact hPA |].
      exact (raw_templateContextOnTail_realizable M hPA
        translation baseTail contextTail htail).
    + apply raw_contextList_cons_tail_member; [exact hPA |].
      exact (ih formula htail hin).
Qed.

Lemma raw_templateContextOnTail_shift : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      translation baseTail context,
  RawContextShift M baseTail baseTail ->
  RawContextShift M
    (rawTemplateContextCodeOnTail translation baseTail context)
    (rawTemplateContextCodeOnTail translation baseTail
      (templateContextShift context)).
Proof.
  intros M hPA translation baseTail context htail.
  induction context as [|formula contextTail ih].
  - cbn [templateContextShift templateContextRename]. exact htail.
  - cbn [templateContextShift templateContextRename].
    apply raw_contextShift_cons; [exact hPA | exact ih |].
    exact (rawTemplateFormula_shift translation formula).
Qed.

(** The advertised endpoint of a constructor does not depend on recursive
    validity.  Only universal elimination and equality elimination need an
    operation trace to select their substitution-generated conclusion. *)
Theorem raw_templateProofOnTail_endpoint : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (baseTail : M) (derivation : TemplateRawProof),
  RawProofEndpoint M (rawTemplateProofCodeOnTail translation baseTail derivation)
    (rawTemplateContextCodeOnTail translation baseTail
      (templateRawContext derivation))
    (rawTemplateFormula translation
      (templateRawConclusion derivation)).
Proof.
  intros M translation baseTail derivation.
  destruct derivation as
    [context formula
    | context antecedent consequent child
    | context antecedent consequent implicationChild antecedentChild
    | context conclusion child
    | context formula
    | context leftFormula rightFormula leftChild rightChild
    | context leftFormula rightFormula child
    | context leftFormula rightFormula child
    | context leftFormula rightFormula child
    | context leftFormula rightFormula child
    | context leftFormula rightFormula conclusion disjunctionChild
        leftChild rightChild
    | context body child
    | context body replacement child
    | context body replacement child
    | context body conclusion existentialChild bodyChild
    | context witness
    | context source target motive equalityChild motiveChild];
    cbn [rawTemplateProofCodeOnTail templateRawContext templateRawConclusion].
  - apply raw_proofAssumption_endpoint.
  - rewrite rawTemplateFormula_imp. apply raw_proofImpI_endpoint.
  - apply raw_proofImpE_endpoint.
  - apply raw_proofBotE_endpoint.
  - rewrite rawTemplateFormula_or, rawTemplateFormula_imp,
      rawTemplateFormula_bot.
    apply raw_proofLem_endpoint.
  - rewrite rawTemplateFormula_and. apply raw_proofAndI_endpoint.
  - apply raw_proofAndE_endpoint.
  - apply raw_proofAndE_endpoint.
  - rewrite rawTemplateFormula_or. apply raw_proofOrI_endpoint.
  - rewrite rawTemplateFormula_or. apply raw_proofOrI_endpoint.
  - apply raw_proofOrE_endpoint.
  - rewrite rawTemplateFormula_all. apply raw_proofAllI_endpoint.
  - apply raw_proofAllE_endpoint.
    exact (rawTemplateFormula_open translation body replacement).
  - rewrite rawTemplateFormula_ex. apply raw_proofExI_endpoint.
  - apply raw_proofExE_endpoint.
  - rewrite rawTemplateFormula_eq. apply raw_proofEqRefl_endpoint.
  - apply raw_proofEqElim_endpoint.
    exact (rawTemplateFormula_open translation motive target).
Qed.

(** Transport an endpoint along the source tree's declarative endpoint
    equations.  Keeping this as a separate lemma makes the coverage
    induction below follow the rule statements almost literally. *)
Lemma raw_templateProofOnTail_endpoint_at : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    baseTail derivation context conclusion,
  templateRawContext derivation = context ->
  templateRawConclusion derivation = conclusion ->
  RawProofEndpoint M
    (rawTemplateProofCodeOnTail translation baseTail derivation)
    (rawTemplateContextCodeOnTail translation baseTail context)
    (rawTemplateFormula translation conclusion).
Proof.
  intros M translation baseTail derivation context conclusion
    hcontext hconclusion.
  subst context conclusion.
  apply raw_templateProofOnTail_endpoint.
Qed.

(** Every valid finite template compiles to proof-wide rule coverage.  Each
    induction hypothesis supplies coverage for a child; the endpoint lemma
    above supplies the exact context and conclusion expected by the public
    raw constructor. *)
Theorem raw_templateProofOnTail_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M) baseTail derivation,
  RawContextListRealizable M baseTail ->
  RawContextShift M baseTail baseTail ->
  TemplateRawProofValid derivation ->
  RawProofRuleCoverage M
    (rawTemplateProofCodeOnTail translation baseTail derivation).
Proof.
  intros M hPA translation baseTail derivation
    htailRealizable htailSelfShift.
  induction derivation as
    [context conclusion
    | context antecedent consequent child ihChild
    | context antecedent consequent implicationChild ihImplication
        antecedentChild ihAntecedent
    | context conclusion child ihChild
    | context body
    | context leftFormula rightFormula leftChild ihLeft
        rightChild ihRight
    | context leftFormula rightFormula child ihChild
    | context leftFormula rightFormula child ihChild
    | context leftFormula rightFormula child ihChild
    | context leftFormula rightFormula child ihChild
    | context leftFormula rightFormula conclusion disjunctionChild
        ihDisjunction leftChild ihLeft rightChild ihRight
    | context body child ihChild
    | context body replacement child ihChild
    | context body replacement child ihChild
    | context body conclusion existentialChild ihExistential
        bodyChild ihBody
    | context witness
    | context source target motive equalityChild ihEquality
        motiveChild ihMotive];
    cbn [TemplateRawProofValid rawTemplateProofCodeOnTail]; intro hvalid.
  - exact (raw_proofAssumption_ruleCoverage M hPA
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateFormula translation conclusion)
      (raw_templateContextOnTail_member M hPA translation baseTail
        context conclusion htailRealizable hvalid)).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofImpI_ruleCoverage M hPA).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail child
        (antecedent :: context) consequent
        hchildContext hchildConclusion) as hendpoint.
      cbn [rawTemplateContextCodeOnTail] in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [himplicationValid [himplicationContext [himplicationConclusion
        [hantecedentValid [hantecedentContext hantecedentConclusion]]]]].
    apply (raw_proofImpE_ruleCoverage M hPA).
    + exact (ihImplication himplicationValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail
        implicationChild context (tfImp antecedent consequent)
        himplicationContext himplicationConclusion) as hendpoint.
      rewrite rawTemplateFormula_imp in hendpoint.
      exact hendpoint.
    + exact (ihAntecedent hantecedentValid).
    + exact (raw_templateProofOnTail_endpoint_at M translation baseTail antecedentChild
        context antecedent hantecedentContext hantecedentConclusion).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofBotE_ruleCoverage M hPA).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail child
        context tfBot hchildContext hchildConclusion) as hendpoint.
      rewrite rawTemplateFormula_bot in hendpoint.
      exact hendpoint.
  - exact (raw_proofLem_ruleCoverage M hPA
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateFormula translation body)).
  - destruct hvalid as
      [hleftValid [hleftContext [hleftConclusion
        [hrightValid [hrightContext hrightConclusion]]]]].
    apply (raw_proofAndI_ruleCoverage M hPA).
    + exact (ihLeft hleftValid).
    + exact (raw_templateProofOnTail_endpoint_at M translation baseTail leftChild
        context leftFormula hleftContext hleftConclusion).
    + exact (ihRight hrightValid).
    + exact (raw_templateProofOnTail_endpoint_at M translation baseTail rightChild
        context rightFormula hrightContext hrightConclusion).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAndE_ruleCoverage M hPA RawAndLeft).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail child
        context (tfAnd leftFormula rightFormula)
        hchildContext hchildConclusion) as hendpoint.
      rewrite rawTemplateFormula_and in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAndE_ruleCoverage M hPA RawAndRight).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail child
        context (tfAnd leftFormula rightFormula)
        hchildContext hchildConclusion) as hendpoint.
      rewrite rawTemplateFormula_and in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofOrI_ruleCoverage M hPA RawOrLeft).
    + exact (ihChild hchildValid).
    + exact (raw_templateProofOnTail_endpoint_at M translation baseTail child
        context leftFormula hchildContext hchildConclusion).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofOrI_ruleCoverage M hPA RawOrRight).
    + exact (ihChild hchildValid).
    + exact (raw_templateProofOnTail_endpoint_at M translation baseTail child
        context rightFormula hchildContext hchildConclusion).
  - destruct hvalid as
      [hdisjunctionValid [hdisjunctionContext [hdisjunctionConclusion
        [hleftValid [hleftContext [hleftConclusion
          [hrightValid [hrightContext hrightConclusion]]]]]]]].
    apply (raw_proofOrE_ruleCoverage M hPA).
    + exact (ihDisjunction hdisjunctionValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail
        disjunctionChild context (tfOr leftFormula rightFormula)
        hdisjunctionContext hdisjunctionConclusion) as hendpoint.
      rewrite rawTemplateFormula_or in hendpoint.
      exact hendpoint.
    + exact (ihLeft hleftValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail leftChild
        (leftFormula :: context) conclusion
        hleftContext hleftConclusion) as hendpoint.
      cbn [rawTemplateContextCodeOnTail] in hendpoint.
      exact hendpoint.
    + exact (ihRight hrightValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail rightChild
        (rightFormula :: context) conclusion
        hrightContext hrightConclusion) as hendpoint.
      cbn [rawTemplateContextCodeOnTail] in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAllI_ruleCoverage M hPA
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateContextCodeOnTail translation baseTail
        (templateContextShift context))).
    + exact (raw_templateContextOnTail_shift M hPA translation baseTail context
        htailSelfShift).
    + exact (ihChild hchildValid).
    + exact (raw_templateProofOnTail_endpoint_at M translation baseTail child
        (templateContextShift context) body
        hchildContext hchildConclusion).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAllE_ruleCoverage M hPA).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail child
        context (tfAll body) hchildContext hchildConclusion) as hendpoint.
      rewrite rawTemplateFormula_all in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofExI_ruleCoverage M hPA
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateFormula translation body)
      (rawTemplateTerm translation replacement)
      (rawTemplateFormula translation
        (templateFormulaOpen replacement body))).
    + exact (rawTemplateFormula_open translation body replacement).
    + exact (ihChild hchildValid).
    + exact (raw_templateProofOnTail_endpoint_at M translation baseTail child
        context (templateFormulaOpen replacement body)
        hchildContext hchildConclusion).
  - destruct hvalid as
      [hexistentialValid [hexistentialContext [hexistentialConclusion
        [hbodyValid [hbodyContext hbodyConclusion]]]]].
    apply (raw_proofExE_ruleCoverage M hPA
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateContextCodeOnTail translation baseTail
        (templateContextShift context))
      (rawTemplateFormula translation body)
      (rawTemplateFormula translation conclusion)
      (rawTemplateFormula translation
        (templateFormulaRename S conclusion))).
    + exact (ihExistential hexistentialValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail
        existentialChild context (tfEx body)
        hexistentialContext hexistentialConclusion) as hendpoint.
      rewrite rawTemplateFormula_ex in hendpoint.
      exact hendpoint.
    + exact (raw_templateContextOnTail_shift M hPA translation baseTail context
        htailSelfShift).
    + exact (rawTemplateFormula_shift translation conclusion).
    + exact (ihBody hbodyValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail bodyChild
        (body :: templateContextShift context)
        (templateFormulaRename S conclusion)
        hbodyContext hbodyConclusion) as hendpoint.
      cbn [rawTemplateContextCodeOnTail] in hendpoint.
      exact hendpoint.
  - exact (raw_proofEqRefl_ruleCoverage M hPA
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateTerm translation witness)).
  - destruct hvalid as
      [hequalityValid [hequalityContext [hequalityConclusion
        [hmotiveValid [hmotiveContext hmotiveConclusion]]]]].
    apply (raw_proofEqElim_ruleCoverage M hPA
      (rawTemplateContextCodeOnTail translation baseTail context)
      (rawTemplateTerm translation source)
      (rawTemplateTerm translation target)
      (rawTemplateFormula translation motive)
      (rawTemplateFormula translation
        (templateFormulaOpen source motive))).
    + exact (ihEquality hequalityValid).
    + pose proof (raw_templateProofOnTail_endpoint_at M translation baseTail
        equalityChild context (tfEq source target)
        hequalityContext hequalityConclusion) as hendpoint.
      rewrite rawTemplateFormula_eq in hendpoint.
      exact hendpoint.
    + exact (rawTemplateFormula_open translation motive source).
    + exact (ihMotive hmotiveValid).
    + exact (raw_templateProofOnTail_endpoint_at M translation baseTail motiveChild
        context (templateFormulaOpen source motive)
        hmotiveContext hmotiveConclusion).
Qed.

(** Public compiler theorem. *)
Corollary raw_templateProofOnTail_localProof : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M) baseTail derivation,
  RawContextListRealizable M baseTail ->
  RawContextShift M baseTail baseTail ->
  TemplateRawProofValid derivation ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseTail
      (templateRawContext derivation))
    (rawTemplateFormula translation
      (templateRawConclusion derivation))
    (rawTemplateProofCodeOnTail translation baseTail derivation).
Proof.
  intros M hPA translation baseTail derivation
    htailRealizable htailSelfShift hvalid.
  split.
  - exact (raw_templateProofOnTail_ruleCoverage M hPA
      translation baseTail derivation
      htailRealizable htailSelfShift hvalid).
  - exact (raw_templateProofOnTail_endpoint M translation baseTail derivation).
Qed.


(** A witnessed PA-axiom context supplies both tail hypotheses without any
    decoding or context weakening. *)
Corollary raw_templateProofOnPAAxiomContext_localProof : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M)
      witnessList baseContext derivation,
  RawCodedPAAxiomWitnessContext M witnessList baseContext ->
  TemplateRawProofValid derivation ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext
      (templateRawContext derivation))
    (rawTemplateFormula translation
      (templateRawConclusion derivation))
    (rawTemplateProofCodeOnTail translation baseContext derivation).
Proof.
  intros M hPA translation witnessList baseContext derivation
    hwitness hvalid.
  apply (raw_templateProofOnTail_localProof M hPA
    translation baseContext derivation).
  - exact (raw_codedPAAxiomWitnessContext_context_realizable M
      witnessList baseContext hwitness).
  - exact (raw_codedPAAxiomWitnessContext_selfShift M hPA
      witnessList baseContext hwitness).
  - exact hvalid.
Qed.

End PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
