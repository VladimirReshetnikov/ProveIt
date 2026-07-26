(**
  Coverage-certified compilation of honest proof templates.

  [RawCodedTemplateSyntax] deliberately keeps named carrier parameters and
  opaque predicate applications outside the ordinary metatheoretic PA
  syntax.  This file is the logical half of their specialization.  A
  [RawCodedTemplateTranslation] assigns model elements to template terms and
  formulas and records only the equations/traces inspected by the seventeen
  natural-deduction rules.  The translated formulas may therefore be
  genuinely nonstandard codes.

  Compilation recurses over the fixed, finite [TemplateRawProof], never over
  a carrier value and never by decoding a translated formula.  Every emitted
  node is built with the public coverage-certified raw constructors.  The
  result is consequently an actual [RawCodedPALocalProofOf], not merely a
  semantic validity claim.

  The concrete translator for model-coded truth predicates is intentionally
  separate.  In particular, the two relational fields below require honest
  represented shift and opening traces; atomic adequacy alone is not silently
  treated as a free-variable bound.
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
  RawCodedProofEqElimConstructor RawCodedPALocalProofExistential.

Import ListNotations.

Module PABoundedRawCodedTemplateProofCompiler.

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

(** The exact logical contract used by the compiler.  There is no equation
    for [tfOpaque]: the concrete specialization is free to implement an
    opaque application by any model-coded formula operation, provided the
    two operation traces at the end of the record are proved. *)
Record RawCodedTemplateTranslation (M : RawPAModel) : Type := {
  rawTemplateTerm : TemplateTerm -> M;
  rawTemplateFormula : TemplateFormula -> M;

  rawTemplateFormula_bot :
    rawTemplateFormula tfBot = rawFormulaBotCode M;
  rawTemplateFormula_eq : forall left right,
    rawTemplateFormula (tfEq left right) =
      rawFormulaEqCode M
        (rawTemplateTerm left) (rawTemplateTerm right);
  rawTemplateFormula_imp : forall left right,
    rawTemplateFormula (tfImp left right) =
      rawFormulaImpCode M
        (rawTemplateFormula left) (rawTemplateFormula right);
  rawTemplateFormula_and : forall left right,
    rawTemplateFormula (tfAnd left right) =
      rawFormulaAndCode M
        (rawTemplateFormula left) (rawTemplateFormula right);
  rawTemplateFormula_or : forall left right,
    rawTemplateFormula (tfOr left right) =
      rawFormulaOrCode M
        (rawTemplateFormula left) (rawTemplateFormula right);
  rawTemplateFormula_all : forall body,
    rawTemplateFormula (tfAll body) =
      rawFormulaAllCode M (rawTemplateFormula body);
  rawTemplateFormula_ex : forall body,
    rawTemplateFormula (tfEx body) =
      rawFormulaExCode M (rawTemplateFormula body);

  rawTemplateFormula_shift : forall formula,
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      (rawTemplateFormula formula)
      (rawTemplateFormula (templateFormulaRename S formula));
  rawTemplateFormula_open : forall body replacement,
    RawCodedFormulaSingleSubstitution M
      (rawTemplateTerm replacement)
      (rawTemplateFormula body)
      (rawTemplateFormula (templateFormulaOpen replacement body))
}.

Arguments rawTemplateTerm {M} _ _.
Arguments rawTemplateFormula {M} _ _.
Arguments rawTemplateFormula_bot {M} _.
Arguments rawTemplateFormula_eq {M} _ _ _.
Arguments rawTemplateFormula_imp {M} _ _ _.
Arguments rawTemplateFormula_and {M} _ _ _.
Arguments rawTemplateFormula_or {M} _ _ _.
Arguments rawTemplateFormula_all {M} _ _.
Arguments rawTemplateFormula_ex {M} _ _.
Arguments rawTemplateFormula_shift {M} _ _.
Arguments rawTemplateFormula_open {M} _ _ _.

(** Contexts remain standard meta-lists even when every element is a
    nonstandard formula code.  Folding structurally is what lets the context
    constructors operate without decoding the carrier. *)
Fixpoint rawTemplateContextCode {M : RawPAModel}
    (translation : RawCodedTemplateTranslation M)
    (context : TemplateContext) : M :=
  match context with
  | [] => raw_zero M
  | formula :: tail =>
      rawListNode M (rawTemplateFormula translation formula)
        (rawTemplateContextCode translation tail)
  end.

Arguments rawTemplateContextCode {M} translation context.

(** Each proof node is assembled from already translated rule fields. *)
Fixpoint rawTemplateProofCode {M : RawPAModel}
    (translation : RawCodedTemplateTranslation M)
    (derivation : TemplateRawProof) : M :=
  match derivation with
  | trpAss context formula =>
      rawProofAssumptionRoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation formula)
  | trpImpI context antecedent consequent child =>
      rawProofImpIRoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation antecedent)
        (rawTemplateFormula translation consequent)
        (rawTemplateProofCode translation child)
  | trpImpE context antecedent consequent implicationChild antecedentChild =>
      rawProofImpERoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation antecedent)
        (rawTemplateFormula translation consequent)
        (rawTemplateProofCode translation implicationChild)
        (rawTemplateProofCode translation antecedentChild)
  | trpBotE context conclusion child =>
      rawProofBotERoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation conclusion)
        (rawTemplateProofCode translation child)
  | trpLem context body =>
      rawProofLemRoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation body)
  | trpAndI context leftFormula rightFormula leftChild rightChild =>
      rawProofAndIRoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCode translation leftChild)
        (rawTemplateProofCode translation rightChild)
  | trpAndE1 context leftFormula rightFormula child =>
      rawProofAndERoot M RawAndLeft
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCode translation child)
  | trpAndE2 context leftFormula rightFormula child =>
      rawProofAndERoot M RawAndRight
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCode translation child)
  | trpOrI1 context leftFormula rightFormula child =>
      rawProofOrIRoot M RawOrLeft
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCode translation child)
  | trpOrI2 context leftFormula rightFormula child =>
      rawProofOrIRoot M RawOrRight
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateProofCode translation child)
  | trpOrE context leftFormula rightFormula conclusion disjunctionChild
      leftChild rightChild =>
      rawProofOrERoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation leftFormula)
        (rawTemplateFormula translation rightFormula)
        (rawTemplateFormula translation conclusion)
        (rawTemplateProofCode translation disjunctionChild)
        (rawTemplateProofCode translation leftChild)
        (rawTemplateProofCode translation rightChild)
  | trpAllI context body child =>
      rawProofAllIRoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation body)
        (rawTemplateProofCode translation child)
  | trpAllE context body replacement child =>
      rawProofAllERoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation body)
        (rawTemplateTerm translation replacement)
        (rawTemplateProofCode translation child)
  | trpExI context body replacement child =>
      rawProofExIRoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation body)
        (rawTemplateTerm translation replacement)
        (rawTemplateProofCode translation child)
  | trpExE context body conclusion existentialChild bodyChild =>
      rawProofExERoot M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation body)
        (rawTemplateFormula translation conclusion)
        (rawTemplateProofCode translation existentialChild)
        (rawTemplateProofCode translation bodyChild)
  | trpEqRefl context witness =>
      rawProofEqReflRoot M
        (rawTemplateContextCode translation context)
        (rawTemplateTerm translation witness)
  | trpEqElim context source target motive equalityChild motiveChild =>
      rawProofEqElimRoot M
        (rawTemplateContextCode translation context)
        (rawTemplateTerm translation source)
        (rawTemplateTerm translation target)
        (rawTemplateFormula translation motive)
        (rawTemplateProofCode translation equalityChild)
        (rawTemplateProofCode translation motiveChild)
  end.

Arguments rawTemplateProofCode {M} translation derivation.

(** ------------------------------------------------------------------
    Structural context facts used by the rule constructors. *)

Lemma raw_templateContext_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation context,
  RawContextListRealizable M
    (rawTemplateContextCode translation context).
Proof.
  intros M hPA translation context.
  induction context as [|formula tail ih]; cbn.
  - exact (raw_contextList_empty_realizable M hPA).
  - exact (raw_contextList_cons_realizable M hPA _ _ ih).
Qed.

Lemma raw_templateContext_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation context formula,
  In formula context ->
  RawContextListMember M
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation formula).
Proof.
  intros M hPA translation context.
  induction context as [|head tail ih]; intros formula hin; cbn in hin |- *.
  - contradiction.
  - destruct hin as [-> | hin].
    + apply raw_contextList_cons_head_member; [exact hPA |].
      exact (raw_templateContext_realizable M hPA translation tail).
    + apply raw_contextList_cons_tail_member; [exact hPA |].
      exact (ih formula hin).
Qed.

Lemma raw_templateContext_shift : forall
    (M : RawPAModel), RawPASatisfies M -> forall translation context,
  RawContextShift M
    (rawTemplateContextCode translation context)
    (rawTemplateContextCode translation (templateContextShift context)).
Proof.
  intros M hPA translation context.
  induction context as [|formula tail ih].
  - cbn [templateContextShift templateContextRename].
    exact (raw_contextShift_empty M hPA).
  - cbn [templateContextShift templateContextRename].
    apply raw_contextShift_cons; [exact hPA | exact ih |].
    exact (rawTemplateFormula_shift translation formula).
Qed.

(** The advertised endpoint of a constructor does not depend on recursive
    validity.  Only universal elimination and equality elimination need an
    operation trace to select their substitution-generated conclusion. *)
Theorem raw_templateProof_endpoint : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (derivation : TemplateRawProof),
  RawProofEndpoint M (rawTemplateProofCode translation derivation)
    (rawTemplateContextCode translation
      (templateRawContext derivation))
    (rawTemplateFormula translation
      (templateRawConclusion derivation)).
Proof.
  intros M translation derivation.
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
    cbn [rawTemplateProofCode templateRawContext templateRawConclusion].
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
Lemma raw_templateProof_endpoint_at : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    derivation context conclusion,
  templateRawContext derivation = context ->
  templateRawConclusion derivation = conclusion ->
  RawProofEndpoint M
    (rawTemplateProofCode translation derivation)
    (rawTemplateContextCode translation context)
    (rawTemplateFormula translation conclusion).
Proof.
  intros M translation derivation context conclusion
    hcontext hconclusion.
  subst context conclusion.
  apply raw_templateProof_endpoint.
Qed.

(** Every valid finite template compiles to proof-wide rule coverage.  Each
    induction hypothesis supplies coverage for a child; the endpoint lemma
    above supplies the exact context and conclusion expected by the public
    raw constructor. *)
Theorem raw_templateProof_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M) derivation,
  TemplateRawProofValid derivation ->
  RawProofRuleCoverage M
    (rawTemplateProofCode translation derivation).
Proof.
  intros M hPA translation derivation.
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
    cbn [TemplateRawProofValid rawTemplateProofCode]; intro hvalid.
  - exact (raw_proofAssumption_ruleCoverage M hPA
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation conclusion)
      (raw_templateContext_member M hPA translation
        context conclusion hvalid)).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofImpI_ruleCoverage M hPA).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProof_endpoint_at M translation child
        (antecedent :: context) consequent
        hchildContext hchildConclusion) as hendpoint.
      cbn [rawTemplateContextCode] in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [himplicationValid [himplicationContext [himplicationConclusion
        [hantecedentValid [hantecedentContext hantecedentConclusion]]]]].
    apply (raw_proofImpE_ruleCoverage M hPA).
    + exact (ihImplication himplicationValid).
    + pose proof (raw_templateProof_endpoint_at M translation
        implicationChild context (tfImp antecedent consequent)
        himplicationContext himplicationConclusion) as hendpoint.
      rewrite rawTemplateFormula_imp in hendpoint.
      exact hendpoint.
    + exact (ihAntecedent hantecedentValid).
    + exact (raw_templateProof_endpoint_at M translation antecedentChild
        context antecedent hantecedentContext hantecedentConclusion).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofBotE_ruleCoverage M hPA).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProof_endpoint_at M translation child
        context tfBot hchildContext hchildConclusion) as hendpoint.
      rewrite rawTemplateFormula_bot in hendpoint.
      exact hendpoint.
  - exact (raw_proofLem_ruleCoverage M hPA
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation body)).
  - destruct hvalid as
      [hleftValid [hleftContext [hleftConclusion
        [hrightValid [hrightContext hrightConclusion]]]]].
    apply (raw_proofAndI_ruleCoverage M hPA).
    + exact (ihLeft hleftValid).
    + exact (raw_templateProof_endpoint_at M translation leftChild
        context leftFormula hleftContext hleftConclusion).
    + exact (ihRight hrightValid).
    + exact (raw_templateProof_endpoint_at M translation rightChild
        context rightFormula hrightContext hrightConclusion).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAndE_ruleCoverage M hPA RawAndLeft).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProof_endpoint_at M translation child
        context (tfAnd leftFormula rightFormula)
        hchildContext hchildConclusion) as hendpoint.
      rewrite rawTemplateFormula_and in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAndE_ruleCoverage M hPA RawAndRight).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProof_endpoint_at M translation child
        context (tfAnd leftFormula rightFormula)
        hchildContext hchildConclusion) as hendpoint.
      rewrite rawTemplateFormula_and in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofOrI_ruleCoverage M hPA RawOrLeft).
    + exact (ihChild hchildValid).
    + exact (raw_templateProof_endpoint_at M translation child
        context leftFormula hchildContext hchildConclusion).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofOrI_ruleCoverage M hPA RawOrRight).
    + exact (ihChild hchildValid).
    + exact (raw_templateProof_endpoint_at M translation child
        context rightFormula hchildContext hchildConclusion).
  - destruct hvalid as
      [hdisjunctionValid [hdisjunctionContext [hdisjunctionConclusion
        [hleftValid [hleftContext [hleftConclusion
          [hrightValid [hrightContext hrightConclusion]]]]]]]].
    apply (raw_proofOrE_ruleCoverage M hPA).
    + exact (ihDisjunction hdisjunctionValid).
    + pose proof (raw_templateProof_endpoint_at M translation
        disjunctionChild context (tfOr leftFormula rightFormula)
        hdisjunctionContext hdisjunctionConclusion) as hendpoint.
      rewrite rawTemplateFormula_or in hendpoint.
      exact hendpoint.
    + exact (ihLeft hleftValid).
    + pose proof (raw_templateProof_endpoint_at M translation leftChild
        (leftFormula :: context) conclusion
        hleftContext hleftConclusion) as hendpoint.
      cbn [rawTemplateContextCode] in hendpoint.
      exact hendpoint.
    + exact (ihRight hrightValid).
    + pose proof (raw_templateProof_endpoint_at M translation rightChild
        (rightFormula :: context) conclusion
        hrightContext hrightConclusion) as hendpoint.
      cbn [rawTemplateContextCode] in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAllI_ruleCoverage M hPA
      (rawTemplateContextCode translation context)
      (rawTemplateContextCode translation
        (templateContextShift context))).
    + exact (raw_templateContext_shift M hPA translation context).
    + exact (ihChild hchildValid).
    + exact (raw_templateProof_endpoint_at M translation child
        (templateContextShift context) body
        hchildContext hchildConclusion).
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAllE_ruleCoverage M hPA).
    + exact (ihChild hchildValid).
    + pose proof (raw_templateProof_endpoint_at M translation child
        context (tfAll body) hchildContext hchildConclusion) as hendpoint.
      rewrite rawTemplateFormula_all in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofExI_ruleCoverage M hPA
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation body)
      (rawTemplateTerm translation replacement)
      (rawTemplateFormula translation
        (templateFormulaOpen replacement body))).
    + exact (rawTemplateFormula_open translation body replacement).
    + exact (ihChild hchildValid).
    + exact (raw_templateProof_endpoint_at M translation child
        context (templateFormulaOpen replacement body)
        hchildContext hchildConclusion).
  - destruct hvalid as
      [hexistentialValid [hexistentialContext [hexistentialConclusion
        [hbodyValid [hbodyContext hbodyConclusion]]]]].
    apply (raw_proofExE_ruleCoverage M hPA
      (rawTemplateContextCode translation context)
      (rawTemplateContextCode translation
        (templateContextShift context))
      (rawTemplateFormula translation body)
      (rawTemplateFormula translation conclusion)
      (rawTemplateFormula translation
        (templateFormulaRename S conclusion))).
    + exact (ihExistential hexistentialValid).
    + pose proof (raw_templateProof_endpoint_at M translation
        existentialChild context (tfEx body)
        hexistentialContext hexistentialConclusion) as hendpoint.
      rewrite rawTemplateFormula_ex in hendpoint.
      exact hendpoint.
    + exact (raw_templateContext_shift M hPA translation context).
    + exact (rawTemplateFormula_shift translation conclusion).
    + exact (ihBody hbodyValid).
    + pose proof (raw_templateProof_endpoint_at M translation bodyChild
        (body :: templateContextShift context)
        (templateFormulaRename S conclusion)
        hbodyContext hbodyConclusion) as hendpoint.
      cbn [rawTemplateContextCode] in hendpoint.
      exact hendpoint.
  - exact (raw_proofEqRefl_ruleCoverage M hPA
      (rawTemplateContextCode translation context)
      (rawTemplateTerm translation witness)).
  - destruct hvalid as
      [hequalityValid [hequalityContext [hequalityConclusion
        [hmotiveValid [hmotiveContext hmotiveConclusion]]]]].
    apply (raw_proofEqElim_ruleCoverage M hPA
      (rawTemplateContextCode translation context)
      (rawTemplateTerm translation source)
      (rawTemplateTerm translation target)
      (rawTemplateFormula translation motive)
      (rawTemplateFormula translation
        (templateFormulaOpen source motive))).
    + exact (ihEquality hequalityValid).
    + pose proof (raw_templateProof_endpoint_at M translation
        equalityChild context (tfEq source target)
        hequalityContext hequalityConclusion) as hendpoint.
      rewrite rawTemplateFormula_eq in hendpoint.
      exact hendpoint.
    + exact (rawTemplateFormula_open translation motive source).
    + exact (ihMotive hmotiveValid).
    + exact (raw_templateProof_endpoint_at M translation motiveChild
        context (templateFormulaOpen source motive)
        hmotiveContext hmotiveConclusion).
Qed.

(** Public compiler theorem. *)
Corollary raw_templateProof_localProof : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M) derivation,
  TemplateRawProofValid derivation ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (templateRawContext derivation))
    (rawTemplateFormula translation
      (templateRawConclusion derivation))
    (rawTemplateProofCode translation derivation).
Proof.
  intros M hPA translation derivation hvalid.
  split.
  - exact (raw_templateProof_ruleCoverage M hPA
      translation derivation hvalid).
  - exact (raw_templateProof_endpoint M translation derivation).
Qed.

End PABoundedRawCodedTemplateProofCompiler.
