(**
  Compile a metatheoretic raw natural-deduction tree after translating its
  terms and formulae into an arbitrary raw PA model.

  The standard quotation compiler is intentionally not enough for dynamic
  truth arguments: a proof template may contain formula parameters whose
  values are nonstandard formula codes.  This module isolates the purely
  logical part of that problem.  A [RawCodedProofTranslation] says that a
  pair of maps from ordinary PA syntax into a raw model commutes with every
  logical constructor used by [RawProof], with de Bruijn shift, and with
  one-place substitution.  No assumption is made about arithmetic axioms or
  about how such a translation is produced.

  Contexts and proof trees are then translated structurally.  The proof code
  is assembled only from the public, coverage-certified constructors for
  tags 0--16.  Consequently every valid [RawProof] yields an actual
  [RawCodedPALocalProofOf], not merely a semantic validity statement.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof RawCodedSyntaxConstructors RawCodedFormulaOperations
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

Module PABoundedRawCodedTranslatedProofCompiler.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
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

(** The contract is deliberately syntax-directed.  In particular, the two
    relational fields below are stronger and more useful than equations to
    an external coding function: they provide exactly the witnesses demanded
    by the arithmetized quantifier and equality-elimination rules. *)
Record RawCodedProofTranslation (M : RawPAModel) : Type := {
  rawTranslatedTerm : term -> M;
  rawTranslatedFormula : formula -> M;

  rawTranslatedFormula_bot :
    rawTranslatedFormula pBot = rawFormulaBotCode M;
  rawTranslatedFormula_eq : forall source target,
    rawTranslatedFormula (pEq source target) =
      rawFormulaEqCode M
        (rawTranslatedTerm source) (rawTranslatedTerm target);
  rawTranslatedFormula_imp : forall antecedent consequent,
    rawTranslatedFormula (pImp antecedent consequent) =
      rawFormulaImpCode M
        (rawTranslatedFormula antecedent)
        (rawTranslatedFormula consequent);
  rawTranslatedFormula_and : forall left right,
    rawTranslatedFormula (pAnd left right) =
      rawFormulaAndCode M
        (rawTranslatedFormula left) (rawTranslatedFormula right);
  rawTranslatedFormula_or : forall left right,
    rawTranslatedFormula (pOr left right) =
      rawFormulaOrCode M
        (rawTranslatedFormula left) (rawTranslatedFormula right);
  rawTranslatedFormula_all : forall body,
    rawTranslatedFormula (pAll body) =
      rawFormulaAllCode M (rawTranslatedFormula body);
  rawTranslatedFormula_ex : forall body,
    rawTranslatedFormula (pEx body) =
      rawFormulaExCode M (rawTranslatedFormula body);

  rawTranslatedFormula_shift : forall body,
    RawCodedFormulaShift M
      (raw_zero M) (rawNumeralValue M 1)
      (rawTranslatedFormula body)
      (rawTranslatedFormula (Formula.rename S body));
  rawTranslatedFormula_substitution : forall body replacement,
    RawCodedFormulaSingleSubstitution M
      (rawTranslatedTerm replacement)
      (rawTranslatedFormula body)
      (rawTranslatedFormula
        (Formula.subst (Formula.instTerm replacement) body))
}.

Arguments rawTranslatedTerm {M} _ _.
Arguments rawTranslatedFormula {M} _ _.
Arguments rawTranslatedFormula_bot {M} _.
Arguments rawTranslatedFormula_eq {M} _ _ _.
Arguments rawTranslatedFormula_imp {M} _ _ _.
Arguments rawTranslatedFormula_and {M} _ _ _.
Arguments rawTranslatedFormula_or {M} _ _ _.
Arguments rawTranslatedFormula_all {M} _ _.
Arguments rawTranslatedFormula_ex {M} _ _.
Arguments rawTranslatedFormula_shift {M} _ _.
Arguments rawTranslatedFormula_substitution {M} _ _ _.

(** Unlike [rawQuotedContextCode], this context code may contain genuinely
    nonstandard formula codes.  It is therefore important that all following
    structural facts are proved from the raw list constructors, without an
    external decoder. *)
Fixpoint rawTranslatedContextCode {M : RawPAModel}
    (translation : RawCodedProofTranslation M) (context : list formula) : M :=
  match context with
  | [] => raw_zero M
  | head :: tail =>
      rawListNode M (rawTranslatedFormula translation head)
        (rawTranslatedContextCode translation tail)
  end.

Arguments rawTranslatedContextCode {M} translation context.

Lemma raw_translatedContext_realizable : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedProofTranslation M) context,
  RawContextListRealizable M
    (rawTranslatedContextCode translation context).
Proof.
  intros M hPA translation context.
  induction context as [|head tail IH]; cbn [rawTranslatedContextCode].
  - exact (raw_contextList_empty_realizable M hPA).
  - exact (raw_contextList_cons_realizable M hPA
      (rawTranslatedContextCode translation tail)
      (rawTranslatedFormula translation head) IH).
Qed.

Lemma raw_translatedContext_member : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedProofTranslation M) context member,
  In member context ->
  RawContextListMember M
    (rawTranslatedContextCode translation context)
    (rawTranslatedFormula translation member).
Proof.
  intros M hPA translation context.
  induction context as [|head tail IH]; intros member hmember.
  - contradiction.
  - cbn [In rawTranslatedContextCode] in hmember |- *.
    destruct hmember as [-> | hmember].
    + apply raw_contextList_cons_head_member; [exact hPA |].
      exact (raw_translatedContext_realizable M hPA translation tail).
    + apply raw_contextList_cons_tail_member; [exact hPA |].
      exact (IH member hmember).
Qed.

(** Context shift is constructed in lockstep with the list spine.  This is
    the context-side reason the compiler works at nonstandard formula codes:
    no appeal to standard quotation or formula-code injectivity occurs. *)
Lemma raw_translatedContext_shift : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedProofTranslation M) context,
  RawContextShift M
    (rawTranslatedContextCode translation context)
    (rawTranslatedContextCode translation
      (map (Formula.rename S) context)).
Proof.
  intros M hPA translation context.
  induction context as [|head tail IH]; cbn [rawTranslatedContextCode].
  - exact (raw_contextShift_empty M hPA).
  - exact (raw_contextShift_cons M hPA
      (rawTranslatedContextCode translation tail)
      (rawTranslatedContextCode translation
        (map (Formula.rename S) tail))
      (rawTranslatedFormula translation head)
      (rawTranslatedFormula translation (Formula.rename S head))
      IH (rawTranslatedFormula_shift translation head)).
Qed.

(** The compiled root mirrors [RawProof] constructor-for-constructor.  Tags
    6/7 and 8/9 are selected through the public projection/injection enums,
    avoiding any duplicate definition of the checker encoding. *)
Fixpoint rawTranslatedProofCode {M : RawPAModel}
    (translation : RawCodedProofTranslation M) (derivation : RawProof) : M :=
  match derivation with
  | RP_ass context conclusion =>
      rawProofAssumptionRoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation conclusion)
  | RP_impI context antecedent consequent child =>
      rawProofImpIRoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation antecedent)
        (rawTranslatedFormula translation consequent)
        (rawTranslatedProofCode translation child)
  | RP_impE context antecedent consequent impChild antecedentChild =>
      rawProofImpERoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation antecedent)
        (rawTranslatedFormula translation consequent)
        (rawTranslatedProofCode translation impChild)
        (rawTranslatedProofCode translation antecedentChild)
  | RP_botE context conclusion child =>
      rawProofBotERoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation conclusion)
        (rawTranslatedProofCode translation child)
  | RP_lem context body =>
      rawProofLemRoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation body)
  | RP_andI context leftFormula rightFormula leftChild rightChild =>
      rawProofAndIRoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation leftFormula)
        (rawTranslatedFormula translation rightFormula)
        (rawTranslatedProofCode translation leftChild)
        (rawTranslatedProofCode translation rightChild)
  | RP_andE1 context leftFormula rightFormula child =>
      rawProofAndERoot M RawAndLeft
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation leftFormula)
        (rawTranslatedFormula translation rightFormula)
        (rawTranslatedProofCode translation child)
  | RP_andE2 context leftFormula rightFormula child =>
      rawProofAndERoot M RawAndRight
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation leftFormula)
        (rawTranslatedFormula translation rightFormula)
        (rawTranslatedProofCode translation child)
  | RP_orI1 context leftFormula rightFormula child =>
      rawProofOrIRoot M RawOrLeft
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation leftFormula)
        (rawTranslatedFormula translation rightFormula)
        (rawTranslatedProofCode translation child)
  | RP_orI2 context leftFormula rightFormula child =>
      rawProofOrIRoot M RawOrRight
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation leftFormula)
        (rawTranslatedFormula translation rightFormula)
        (rawTranslatedProofCode translation child)
  | RP_orE context leftFormula rightFormula conclusion disjunctionChild
      leftChild rightChild =>
      rawProofOrERoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation leftFormula)
        (rawTranslatedFormula translation rightFormula)
        (rawTranslatedFormula translation conclusion)
        (rawTranslatedProofCode translation disjunctionChild)
        (rawTranslatedProofCode translation leftChild)
        (rawTranslatedProofCode translation rightChild)
  | RP_allI context body child =>
      rawProofAllIRoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation body)
        (rawTranslatedProofCode translation child)
  | RP_allE context body replacement child =>
      rawProofAllERoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation body)
        (rawTranslatedTerm translation replacement)
        (rawTranslatedProofCode translation child)
  | RP_exI context body replacement child =>
      rawProofExIRoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation body)
        (rawTranslatedTerm translation replacement)
        (rawTranslatedProofCode translation child)
  | RP_exE context body conclusion existentialChild bodyChild =>
      rawProofExERoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedFormula translation body)
        (rawTranslatedFormula translation conclusion)
        (rawTranslatedProofCode translation existentialChild)
        (rawTranslatedProofCode translation bodyChild)
  | RP_eqRefl context witness =>
      rawProofEqReflRoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedTerm translation witness)
  | RP_eqElim context source target body equalityChild bodyChild =>
      rawProofEqElimRoot M
        (rawTranslatedContextCode translation context)
        (rawTranslatedTerm translation source)
        (rawTranslatedTerm translation target)
        (rawTranslatedFormula translation body)
        (rawTranslatedProofCode translation equalityChild)
        (rawTranslatedProofCode translation bodyChild)
  end.

Arguments rawTranslatedProofCode {M} translation derivation.

(** Endpoint correctness does not require validity of the source tree: every
    public raw constructor advertises its endpoint directly.  The only
    relational side conditions are target substitution for [allE] and
    [eqElim], supplied by the translation contract. *)
Theorem raw_translatedProof_endpoint : forall
    (M : RawPAModel) (translation : RawCodedProofTranslation M) derivation,
  RawProofEndpoint M
    (rawTranslatedProofCode translation derivation)
    (rawTranslatedContextCode translation (rawContext derivation))
    (rawTranslatedFormula translation (rawConclusion derivation)).
Proof.
  intros M translation derivation.
  destruct derivation as
    [context conclusion
    | context antecedent consequent child
    | context antecedent consequent impChild antecedentChild
    | context conclusion child
    | context body
    | context left right leftChild rightChild
    | context left right child
    | context left right child
    | context left right child
    | context left right child
    | context left right conclusion disjunctionChild leftChild rightChild
    | context body child
    | context body replacement child
    | context body replacement child
    | context body conclusion existentialChild bodyChild
    | context witness
    | context source target body equalityChild bodyChild];
    cbn [rawTranslatedProofCode rawContext rawConclusion].
  - apply raw_proofAssumption_endpoint.
  - rewrite rawTranslatedFormula_imp.
    apply raw_proofImpI_endpoint.
  - apply raw_proofImpE_endpoint.
  - apply raw_proofBotE_endpoint.
  - rewrite rawTranslatedFormula_or, rawTranslatedFormula_imp,
      rawTranslatedFormula_bot.
    apply raw_proofLem_endpoint.
  - rewrite rawTranslatedFormula_and.
    apply raw_proofAndI_endpoint.
  - apply raw_proofAndE_endpoint.
  - apply raw_proofAndE_endpoint.
  - rewrite rawTranslatedFormula_or.
    apply raw_proofOrI_endpoint.
  - rewrite rawTranslatedFormula_or.
    apply raw_proofOrI_endpoint.
  - apply raw_proofOrE_endpoint.
  - rewrite rawTranslatedFormula_all.
    apply raw_proofAllI_endpoint.
  - apply raw_proofAllE_endpoint.
    exact (rawTranslatedFormula_substitution translation body replacement).
  - rewrite rawTranslatedFormula_ex.
    apply raw_proofExI_endpoint.
  - apply raw_proofExE_endpoint.
  - rewrite rawTranslatedFormula_eq.
    apply raw_proofEqRefl_endpoint.
  - apply raw_proofEqElim_endpoint.
    exact (rawTranslatedFormula_substitution translation body target).
Qed.

(** A small transport form of endpoint correctness keeps the coverage proof
    below readable.  Source validity records premise endpoints as equations;
    this lemma turns those equations directly into endpoints of the compiled
    children. *)
Lemma raw_translatedProof_endpoint_at : forall
    (M : RawPAModel) (translation : RawCodedProofTranslation M)
    derivation context conclusion,
  rawContext derivation = context ->
  rawConclusion derivation = conclusion ->
  RawProofEndpoint M
    (rawTranslatedProofCode translation derivation)
    (rawTranslatedContextCode translation context)
    (rawTranslatedFormula translation conclusion).
Proof.
  intros M translation derivation context conclusion
    hcontext hconclusion.
  subst context conclusion.
  apply raw_translatedProof_endpoint.
Qed.

(** Structural validity is precisely what is needed to combine the local
    constructor certificates.  Notice that the induction hypotheses provide
    proof-wide coverage, while [raw_translatedProof_endpoint_at] supplies the
    exact child endpoints expected by each parent constructor. *)
Theorem raw_translatedProof_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedProofTranslation M) derivation,
  RawProofValid derivation ->
  RawProofRuleCoverage M
    (rawTranslatedProofCode translation derivation).
Proof.
  intros M hPA translation derivation.
  induction derivation as
    [context conclusion
    | context antecedent consequent child IHchild
    | context antecedent consequent impChild IHimp
        antecedentChild IHantecedent
    | context conclusion child IHchild
    | context body
    | context leftFormula rightFormula leftChild IHleft
        rightChild IHright
    | context leftFormula rightFormula child IHchild
    | context leftFormula rightFormula child IHchild
    | context leftFormula rightFormula child IHchild
    | context leftFormula rightFormula child IHchild
    | context leftFormula rightFormula conclusion disjunctionChild
        IHdisjunction leftChild IHleft rightChild IHright
    | context body child IHchild
    | context body replacement child IHchild
    | context body replacement child IHchild
    | context body conclusion existentialChild IHexistential
        bodyChild IHbody
    | context witness
    | context source target body equalityChild IHequality
        bodyChild IHbody];
    cbn [RawProofValid rawTranslatedProofCode]; intro hvalid.
  - exact (raw_proofAssumption_ruleCoverage M hPA
      (rawTranslatedContextCode translation context)
      (rawTranslatedFormula translation conclusion)
      (raw_translatedContext_member M hPA translation
        context conclusion hvalid)).
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofImpI_ruleCoverage M hPA).
    + exact (IHchild hchildValid).
    + pose proof (raw_translatedProof_endpoint_at M translation child
        (antecedent :: context) consequent
        hchildContext hchildConclusion) as hendpoint.
      cbn [rawTranslatedContextCode] in hendpoint.
      exact hendpoint.
  - destruct hvalid as
      [himpValid [himpContext [himpConclusion
        [hantecedentValid [hantecedentContext hantecedentConclusion]]]]].
    apply (raw_proofImpE_ruleCoverage M hPA).
    + exact (IHimp himpValid).
    + pose proof (raw_translatedProof_endpoint_at M translation impChild
        context (pImp antecedent consequent)
        himpContext himpConclusion) as hendpoint.
      rewrite rawTranslatedFormula_imp in hendpoint.
      exact hendpoint.
    + exact (IHantecedent hantecedentValid).
    + exact (raw_translatedProof_endpoint_at M translation antecedentChild
        context antecedent hantecedentContext hantecedentConclusion).
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofBotE_ruleCoverage M hPA).
    + exact (IHchild hchildValid).
    + pose proof (raw_translatedProof_endpoint_at M translation child
        context pBot hchildContext hchildConclusion) as hendpoint.
      rewrite rawTranslatedFormula_bot in hendpoint.
      exact hendpoint.
  - exact (raw_proofLem_ruleCoverage M hPA
      (rawTranslatedContextCode translation context)
      (rawTranslatedFormula translation body)).
  - destruct hvalid as
      [hleftValid [hleftContext [hleftConclusion
        [hrightValid [hrightContext hrightConclusion]]]]].
    apply (raw_proofAndI_ruleCoverage M hPA).
    + exact (IHleft hleftValid).
    + exact (raw_translatedProof_endpoint_at M translation leftChild
        context leftFormula hleftContext hleftConclusion).
    + exact (IHright hrightValid).
    + exact (raw_translatedProof_endpoint_at M translation rightChild
        context rightFormula hrightContext hrightConclusion).
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAndE_ruleCoverage M hPA RawAndLeft).
    + exact (IHchild hchildValid).
    + pose proof (raw_translatedProof_endpoint_at M translation child
        context (pAnd leftFormula rightFormula)
        hchildContext hchildConclusion) as hendpoint.
      rewrite rawTranslatedFormula_and in hendpoint.
      exact hendpoint.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAndE_ruleCoverage M hPA RawAndRight).
    + exact (IHchild hchildValid).
    + pose proof (raw_translatedProof_endpoint_at M translation child
        context (pAnd leftFormula rightFormula)
        hchildContext hchildConclusion) as hendpoint.
      rewrite rawTranslatedFormula_and in hendpoint.
      exact hendpoint.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofOrI_ruleCoverage M hPA RawOrLeft).
    + exact (IHchild hchildValid).
    + exact (raw_translatedProof_endpoint_at M translation child
        context leftFormula hchildContext hchildConclusion).
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofOrI_ruleCoverage M hPA RawOrRight).
    + exact (IHchild hchildValid).
    + exact (raw_translatedProof_endpoint_at M translation child
        context rightFormula hchildContext hchildConclusion).
  - destruct hvalid as
      [hdisjunctionValid [hdisjunctionContext [hdisjunctionConclusion
        [hleftValid [hleftContext [hleftConclusion
          [hrightValid [hrightContext hrightConclusion]]]]]]]].
    apply (raw_proofOrE_ruleCoverage M hPA).
    + exact (IHdisjunction hdisjunctionValid).
    + pose proof (raw_translatedProof_endpoint_at M translation
        disjunctionChild context (pOr leftFormula rightFormula)
        hdisjunctionContext hdisjunctionConclusion) as hendpoint.
      rewrite rawTranslatedFormula_or in hendpoint.
      exact hendpoint.
    + exact (IHleft hleftValid).
    + pose proof (raw_translatedProof_endpoint_at M translation leftChild
        (leftFormula :: context) conclusion
        hleftContext hleftConclusion) as hendpoint.
      cbn [rawTranslatedContextCode] in hendpoint.
      exact hendpoint.
    + exact (IHright hrightValid).
    + pose proof (raw_translatedProof_endpoint_at M translation rightChild
        (rightFormula :: context) conclusion
        hrightContext hrightConclusion) as hendpoint.
      cbn [rawTranslatedContextCode] in hendpoint.
      exact hendpoint.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAllI_ruleCoverage M hPA
      (rawTranslatedContextCode translation context)
      (rawTranslatedContextCode translation
        (map (Formula.rename S) context))).
    + exact (raw_translatedContext_shift M hPA translation context).
    + exact (IHchild hchildValid).
    + exact (raw_translatedProof_endpoint_at M translation child
        (map (Formula.rename S) context) body
        hchildContext hchildConclusion).
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofAllE_ruleCoverage M hPA).
    + exact (IHchild hchildValid).
    + pose proof (raw_translatedProof_endpoint_at M translation child
        context (pAll body) hchildContext hchildConclusion) as hendpoint.
      rewrite rawTranslatedFormula_all in hendpoint.
      exact hendpoint.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    apply (raw_proofExI_ruleCoverage M hPA
      (rawTranslatedContextCode translation context)
      (rawTranslatedFormula translation body)
      (rawTranslatedTerm translation replacement)
      (rawTranslatedFormula translation
        (Formula.subst (Formula.instTerm replacement) body))).
    + exact (rawTranslatedFormula_substitution
        translation body replacement).
    + exact (IHchild hchildValid).
    + exact (raw_translatedProof_endpoint_at M translation child
        context (Formula.subst (Formula.instTerm replacement) body)
        hchildContext hchildConclusion).
  - destruct hvalid as
      [hexistentialValid [hexistentialContext [hexistentialConclusion
        [hbodyValid [hbodyContext hbodyConclusion]]]]].
    apply (raw_proofExE_ruleCoverage M hPA
      (rawTranslatedContextCode translation context)
      (rawTranslatedContextCode translation
        (map (Formula.rename S) context))
      (rawTranslatedFormula translation body)
      (rawTranslatedFormula translation conclusion)
      (rawTranslatedFormula translation (Formula.rename S conclusion))).
    + exact (IHexistential hexistentialValid).
    + pose proof (raw_translatedProof_endpoint_at M translation
        existentialChild context (pEx body)
        hexistentialContext hexistentialConclusion) as hendpoint.
      rewrite rawTranslatedFormula_ex in hendpoint.
      exact hendpoint.
    + exact (raw_translatedContext_shift M hPA translation context).
    + exact (rawTranslatedFormula_shift translation conclusion).
    + exact (IHbody hbodyValid).
    + pose proof (raw_translatedProof_endpoint_at M translation bodyChild
        (body :: map (Formula.rename S) context)
        (Formula.rename S conclusion)
        hbodyContext hbodyConclusion) as hendpoint.
      cbn [rawTranslatedContextCode] in hendpoint.
      exact hendpoint.
  - exact (raw_proofEqRefl_ruleCoverage M hPA
      (rawTranslatedContextCode translation context)
      (rawTranslatedTerm translation witness)).
  - destruct hvalid as
      [hequalityValid [hequalityContext [hequalityConclusion
        [hbodyValid [hbodyContext hbodyConclusion]]]]].
    apply (raw_proofEqElim_ruleCoverage M hPA
      (rawTranslatedContextCode translation context)
      (rawTranslatedTerm translation source)
      (rawTranslatedTerm translation target)
      (rawTranslatedFormula translation body)
      (rawTranslatedFormula translation
        (Formula.subst (Formula.instTerm source) body))).
    + exact (IHequality hequalityValid).
    + pose proof (raw_translatedProof_endpoint_at M translation
        equalityChild context (pEq source target)
        hequalityContext hequalityConclusion) as hendpoint.
      rewrite rawTranslatedFormula_eq in hendpoint.
      exact hendpoint.
    + exact (rawTranslatedFormula_substitution translation body source).
    + exact (IHbody hbodyValid).
    + exact (raw_translatedProof_endpoint_at M translation bodyChild
        context (Formula.subst (Formula.instTerm source) body)
        hbodyContext hbodyConclusion).
Qed.

(** The final package is the exact local proof predicate consumed by the
    later PA-axiom and certificate compilers. *)
Corollary raw_translatedProof_localProof : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedProofTranslation M) derivation,
  RawProofValid derivation ->
  RawCodedPALocalProofOf M
    (rawTranslatedContextCode translation (rawContext derivation))
    (rawTranslatedFormula translation (rawConclusion derivation))
    (rawTranslatedProofCode translation derivation).
Proof.
  intros M hPA translation derivation hvalid.
  split.
  - exact (raw_translatedProof_ruleCoverage M hPA
      translation derivation hvalid).
  - exact (raw_translatedProof_endpoint M translation derivation).
Qed.

End PABoundedRawCodedTranslatedProofCompiler.
