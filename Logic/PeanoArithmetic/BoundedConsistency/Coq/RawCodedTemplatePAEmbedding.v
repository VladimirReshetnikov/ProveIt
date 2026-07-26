(**
  Embed ordinary PA derivations into the model-coded template compiler.

  Template syntax contains named carrier parameters and opaque predicates,
  but ordinary PA axioms contain neither.  This module makes that boundary
  explicit.  First it embeds every constructor of [CodedProof.RawProof] into
  the corresponding template constructor and proves that contexts,
  conclusions, and declarative validity are preserved.  Next an agreement
  record says that a concrete template translation interprets the embedded
  PA fragment by the existing standard raw quotations.

  The final extraction theorem starts from an ordinary finite [BProv] proof.
  Its witnessed axiom context is still built by
  [raw_codedPAAxiomWitnessContext_standard]; only the proof tree is routed
  through the template compiler.  Thus opaque template formulas may occur in
  other templates, but are never silently admitted as PA axioms here.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency CodedProof RawCodedSyntaxConstructors
  RawCodedProofConstructors RawCodedRestrictedProofStandardAdequacy
  RawCodedRestrictedPAProof RawCodedPAProvability
  RawCodedTemplateSyntax RawCodedTemplateProofCompiler.

Import ListNotations.

Module PABoundedRawCodedTemplatePAEmbedding.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedRestrictedProofStandardAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.

(** ------------------------------------------------------------------
    Constructor-for-constructor embedding of ordinary raw proofs. *)

Fixpoint embedRawProof (derivation : RawProof) : TemplateRawProof :=
  match derivation with
  | RP_ass context formula =>
      trpAss (embedPAContext context) (embedPAFormula formula)
  | RP_impI context antecedent consequent child =>
      trpImpI (embedPAContext context)
        (embedPAFormula antecedent) (embedPAFormula consequent)
        (embedRawProof child)
  | RP_impE context antecedent consequent implicationChild
      antecedentChild =>
      trpImpE (embedPAContext context)
        (embedPAFormula antecedent) (embedPAFormula consequent)
        (embedRawProof implicationChild)
        (embedRawProof antecedentChild)
  | RP_botE context conclusion child =>
      trpBotE (embedPAContext context) (embedPAFormula conclusion)
        (embedRawProof child)
  | RP_lem context body =>
      trpLem (embedPAContext context) (embedPAFormula body)
  | RP_andI context leftFormula rightFormula leftChild rightChild =>
      trpAndI (embedPAContext context)
        (embedPAFormula leftFormula) (embedPAFormula rightFormula)
        (embedRawProof leftChild) (embedRawProof rightChild)
  | RP_andE1 context leftFormula rightFormula child =>
      trpAndE1 (embedPAContext context)
        (embedPAFormula leftFormula) (embedPAFormula rightFormula)
        (embedRawProof child)
  | RP_andE2 context leftFormula rightFormula child =>
      trpAndE2 (embedPAContext context)
        (embedPAFormula leftFormula) (embedPAFormula rightFormula)
        (embedRawProof child)
  | RP_orI1 context leftFormula rightFormula child =>
      trpOrI1 (embedPAContext context)
        (embedPAFormula leftFormula) (embedPAFormula rightFormula)
        (embedRawProof child)
  | RP_orI2 context leftFormula rightFormula child =>
      trpOrI2 (embedPAContext context)
        (embedPAFormula leftFormula) (embedPAFormula rightFormula)
        (embedRawProof child)
  | RP_orE context leftFormula rightFormula conclusion disjunctionChild
      leftChild rightChild =>
      trpOrE (embedPAContext context)
        (embedPAFormula leftFormula) (embedPAFormula rightFormula)
        (embedPAFormula conclusion)
        (embedRawProof disjunctionChild)
        (embedRawProof leftChild) (embedRawProof rightChild)
  | RP_allI context body child =>
      trpAllI (embedPAContext context) (embedPAFormula body)
        (embedRawProof child)
  | RP_allE context body replacement child =>
      trpAllE (embedPAContext context) (embedPAFormula body)
        (embedPATerm replacement) (embedRawProof child)
  | RP_exI context body replacement child =>
      trpExI (embedPAContext context) (embedPAFormula body)
        (embedPATerm replacement) (embedRawProof child)
  | RP_exE context body conclusion existentialChild bodyChild =>
      trpExE (embedPAContext context)
        (embedPAFormula body) (embedPAFormula conclusion)
        (embedRawProof existentialChild) (embedRawProof bodyChild)
  | RP_eqRefl context witness =>
      trpEqRefl (embedPAContext context) (embedPATerm witness)
  | RP_eqElim context source target motive equalityChild motiveChild =>
      trpEqElim (embedPAContext context)
        (embedPATerm source) (embedPATerm target)
        (embedPAFormula motive)
        (embedRawProof equalityChild) (embedRawProof motiveChild)
  end.

Lemma embedRawProof_context : forall derivation,
  templateRawContext (embedRawProof derivation) =
  embedPAContext (rawContext derivation).
Proof. intros derivation; destruct derivation; reflexivity. Qed.

Lemma embedRawProof_conclusion : forall derivation,
  templateRawConclusion (embedRawProof derivation) =
  embedPAFormula (rawConclusion derivation).
Proof.
  intros derivation; destruct derivation;
    cbn [embedRawProof templateRawConclusion rawConclusion];
    try reflexivity.
  - symmetry. apply embedPAFormula_instTerm.
  - symmetry. apply embedPAFormula_instTerm.
Qed.

(** Validity preservation is the point where the de Bruijn laws proved for
    [embedPAFormula] matter.  Universal introduction and existential
    elimination use context shift; existential introduction and equality
    elimination use capture-avoiding opening. *)
Theorem embedRawProof_valid : forall derivation,
  RawProofValid derivation ->
  TemplateRawProofValid (embedRawProof derivation).
Proof.
  intro derivation.
  induction derivation as
    [context formula
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
    cbn [RawProofValid TemplateRawProofValid embedRawProof]; intro hvalid.
  - apply in_map. exact hvalid.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    repeat split.
    + exact (ihChild hchildValid).
    + rewrite embedRawProof_context, hchildContext. reflexivity.
    + rewrite embedRawProof_conclusion, hchildConclusion. reflexivity.
  - destruct hvalid as
      [himplicationValid [himplicationContext [himplicationConclusion
        [hantecedentValid [hantecedentContext hantecedentConclusion]]]]].
    repeat split.
    + exact (ihImplication himplicationValid).
    + now rewrite embedRawProof_context, himplicationContext.
    + now rewrite embedRawProof_conclusion, himplicationConclusion.
    + exact (ihAntecedent hantecedentValid).
    + now rewrite embedRawProof_context, hantecedentContext.
    + now rewrite embedRawProof_conclusion, hantecedentConclusion.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    repeat split.
    + exact (ihChild hchildValid).
    + now rewrite embedRawProof_context, hchildContext.
    + now rewrite embedRawProof_conclusion, hchildConclusion.
  - exact I.
  - destruct hvalid as
      [hleftValid [hleftContext [hleftConclusion
        [hrightValid [hrightContext hrightConclusion]]]]].
    repeat split.
    + exact (ihLeft hleftValid).
    + now rewrite embedRawProof_context, hleftContext.
    + now rewrite embedRawProof_conclusion, hleftConclusion.
    + exact (ihRight hrightValid).
    + now rewrite embedRawProof_context, hrightContext.
    + now rewrite embedRawProof_conclusion, hrightConclusion.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    repeat split.
    + exact (ihChild hchildValid).
    + now rewrite embedRawProof_context, hchildContext.
    + now rewrite embedRawProof_conclusion, hchildConclusion.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    repeat split.
    + exact (ihChild hchildValid).
    + now rewrite embedRawProof_context, hchildContext.
    + now rewrite embedRawProof_conclusion, hchildConclusion.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    repeat split.
    + exact (ihChild hchildValid).
    + now rewrite embedRawProof_context, hchildContext.
    + now rewrite embedRawProof_conclusion, hchildConclusion.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    repeat split.
    + exact (ihChild hchildValid).
    + now rewrite embedRawProof_context, hchildContext.
    + now rewrite embedRawProof_conclusion, hchildConclusion.
  - destruct hvalid as
      [hdisjunctionValid [hdisjunctionContext [hdisjunctionConclusion
        [hleftValid [hleftContext [hleftConclusion
          [hrightValid [hrightContext hrightConclusion]]]]]]]].
    repeat split.
    + exact (ihDisjunction hdisjunctionValid).
    + now rewrite embedRawProof_context, hdisjunctionContext.
    + now rewrite embedRawProof_conclusion, hdisjunctionConclusion.
    + exact (ihLeft hleftValid).
    + rewrite embedRawProof_context, hleftContext. reflexivity.
    + now rewrite embedRawProof_conclusion, hleftConclusion.
    + exact (ihRight hrightValid).
    + rewrite embedRawProof_context, hrightContext. reflexivity.
    + now rewrite embedRawProof_conclusion, hrightConclusion.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    repeat split.
    + exact (ihChild hchildValid).
    + rewrite embedRawProof_context, hchildContext,
        embedPAContext_shift. reflexivity.
    + now rewrite embedRawProof_conclusion, hchildConclusion.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    repeat split.
    + exact (ihChild hchildValid).
    + now rewrite embedRawProof_context, hchildContext.
    + now rewrite embedRawProof_conclusion, hchildConclusion.
  - destruct hvalid as [hchildValid [hchildContext hchildConclusion]].
    repeat split.
    + exact (ihChild hchildValid).
    + now rewrite embedRawProof_context, hchildContext.
    + rewrite embedRawProof_conclusion, hchildConclusion.
      apply embedPAFormula_instTerm.
  - destruct hvalid as
      [hexistentialValid [hexistentialContext [hexistentialConclusion
        [hbodyValid [hbodyContext hbodyConclusion]]]]].
    repeat split.
    + exact (ihExistential hexistentialValid).
    + now rewrite embedRawProof_context, hexistentialContext.
    + now rewrite embedRawProof_conclusion, hexistentialConclusion.
    + exact (ihBody hbodyValid).
    + rewrite embedRawProof_context, hbodyContext.
      change (embedPAFormula body ::
        embedPAContext (map (Formula.rename S) context) =
        embedPAFormula body ::
        templateContextShift (embedPAContext context)).
      f_equal. apply embedPAContext_shift.
    + rewrite embedRawProof_conclusion, hbodyConclusion.
      apply embedPAFormula_rename.
  - exact I.
  - destruct hvalid as
      [hequalityValid [hequalityContext [hequalityConclusion
        [hmotiveValid [hmotiveContext hmotiveConclusion]]]]].
    repeat split.
    + exact (ihEquality hequalityValid).
    + now rewrite embedRawProof_context, hequalityContext.
    + now rewrite embedRawProof_conclusion, hequalityConclusion.
    + exact (ihMotive hmotiveValid).
    + now rewrite embedRawProof_context, hmotiveContext.
    + rewrite embedRawProof_conclusion, hmotiveConclusion.
      apply embedPAFormula_instTerm.
Qed.

(** ------------------------------------------------------------------
    Agreement of a concrete translation with standard PA quotation. *)

Record RawCodedTemplatePAAgreement (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M) : Prop := {
  rawTemplateTerm_embedPA : forall input,
    rawTemplateTerm translation (embedPATerm input) =
      rawQuotedTermCode M input;
  rawTemplateFormula_embedPA : forall input,
    rawTemplateFormula translation (embedPAFormula input) =
      rawQuotedFormulaCode M input
}.

Arguments rawTemplateTerm_embedPA {M translation} _ input.
Arguments rawTemplateFormula_embedPA {M translation} _ input.

Lemma raw_templateContextCode_embedPA : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall context,
  rawTemplateContextCode translation (embedPAContext context) =
    rawQuotedContextCode M context.
Proof.
  intros M translation hagreement context.
  induction context as [|formula tail ih].
  - reflexivity.
  - change (rawListNode M
      (rawTemplateFormula translation (embedPAFormula formula))
      (rawTemplateContextCode translation (embedPAContext tail)) =
      rawListNode M (rawQuotedFormulaCode M formula)
        (rawQuotedContextCode M tail)).
    rewrite (rawTemplateFormula_embedPA hagreement formula), ih.
    reflexivity.
Qed.

Corollary raw_templateContextCode_embedPA_numeral : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall context,
  rawTemplateContextCode translation (embedPAContext context) =
    rawNumeralValue M (contextCode context).
Proof.
  intros M hPA translation hagreement context.
  rewrite (raw_templateContextCode_embedPA M translation
    hagreement context).
  apply rawQuotedContextCode_standard. exact hPA.
Qed.

(** With context quotation reduced to its numeral form, every emitted
    constructor payload agrees with the established standard proof code.
    This lemma is useful when a consumer wants the old standard certificate
    code, even though the extraction theorem below only needs endpoint and
    coverage agreement. *)
Theorem raw_templateProofCode_embedPA : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall derivation,
  rawTemplateProofCode translation (embedRawProof derivation) =
    rawQuotedProofCode M derivation.
Proof.
  intros M hPA translation hagreement derivation.
  induction derivation;
    cbn [embedRawProof rawTemplateProofCode rawQuotedProofCode].
  all: repeat rewrite (raw_templateContextCode_embedPA_numeral
    M hPA translation hagreement).
  all: repeat rewrite (rawTemplateTerm_embedPA hagreement).
  all: repeat rewrite (rawTemplateFormula_embedPA hagreement).
  all: repeat match goal with
  | ih : rawTemplateProofCode ?concreteTranslation
      (embedRawProof ?child) = _ |- _ =>
      rewrite ih
  end.
  all: reflexivity.
Qed.

(** ------------------------------------------------------------------
    Reattach the standard witnessed PA-axiom base. *)

Definition rawTemplatePAProofCertificate (M : RawPAModel)
    (translation : RawCodedTemplateTranslation M)
    (witnesses : list PAAxiomWitness) (derivation : RawProof) : M :=
  rawCodeList3 M (rawNumeralValue M 0)
    (rawQuotedPAAxiomWitnessList M witnesses)
    (rawTemplateProofCode translation (embedRawProof derivation)).

Arguments rawTemplatePAProofCertificate
  M translation witnesses derivation : clear implicits.

(** The finite source context is restricted to witnessed ordinary PA axioms.
    Agreement rewrites the template compiler's structural context to the
    standard quoted context accepted by the existing witness traversal. *)
Theorem raw_codedTemplatePAProofOf_standard : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses derivation,
  RawProofValid derivation ->
  rawContext derivation = map witnessedAxiom witnesses ->
  RawCodedPAProofOf M
    (rawTemplateFormula translation
      (embedPAFormula (rawConclusion derivation)))
    (rawTemplatePAProofCertificate M translation witnesses derivation).
Proof.
  intros M hPA translation hagreement witnesses derivation
    hvalid hcontext.
  pose proof (raw_templateProof_localProof M hPA translation
    (embedRawProof derivation) (embedRawProof_valid derivation hvalid))
    as [hcoverage hendpoint].
  rewrite embedRawProof_context in hendpoint.
  rewrite hcontext in hendpoint.
  rewrite (raw_templateContextCode_embedPA M translation
    hagreement (map witnessedAxiom witnesses)) in hendpoint.
  rewrite embedRawProof_conclusion in hendpoint.
  exists (rawQuotedPAAxiomWitnessList M witnesses),
    (rawTemplateProofCode translation (embedRawProof derivation)),
    (rawQuotedContextCode M (map witnessedAxiom witnesses)).
  split; [reflexivity |].
  repeat split.
  - exact (raw_codedPAAxiomWitnessContext_standard M hPA witnesses).
  - exact hcoverage.
  - exact hendpoint.
Qed.

(** Template-routed analogue of [raw_codedPAProofOf_of_BProv].  The target
    is phrased using the concrete translation so it remains useful even when
    that translation also has dynamic, opaque cases elsewhere. *)
Theorem raw_codedTemplatePAProofOf_of_BProv : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall phi,
  Formula.BProv Formula.Ax_s [] phi ->
  exists certificate : M,
    RawCodedPAProofOf M
      (rawTemplateFormula translation (embedPAFormula phi)) certificate.
Proof.
  intros M hPA translation hagreement phi
    (axioms & haxioms & hprov).
  rewrite app_nil_r in hprov.
  destruct (Ax_s_list_has_witnesses axioms haxioms)
    as [witnesses hwitnesses].
  rewrite <- hwitnesses in hprov.
  destruct (ProvTree_complete _ _ hprov) as [derivation _].
  set (rawDerivation := rawOfProvTree derivation).
  exists (rawTemplatePAProofCertificate M translation
    witnesses rawDerivation).
  pose proof (raw_codedTemplatePAProofOf_standard M hPA
    translation hagreement witnesses rawDerivation
    (RawProofValid_rawOfProvTree
      (map witnessedAxiom witnesses) phi derivation)) as hcertificate.
  assert (hrawContext : rawContext rawDerivation =
      map witnessedAxiom witnesses).
  {
    unfold rawDerivation.
    rewrite rawOfProvTree_context. reflexivity.
  }
  specialize (hcertificate hrawContext).
  unfold rawDerivation in hcertificate.
  rewrite rawOfProvTree_conclusion in hcertificate.
  exact hcertificate.
Qed.

End PABoundedRawCodedTemplatePAEmbedding.
