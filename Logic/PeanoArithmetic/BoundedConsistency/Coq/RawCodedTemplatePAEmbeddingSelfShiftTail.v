(**
  Route a fixed ordinary PA theorem through the template compiler above an
  existing witnessed PA-axiom context.

  [RawCodedTemplatePAEmbedding] embeds an ordinary proof constructor by
  constructor, but its final certificate starts from the empty coded context.
  [RawCodedTemplateProofCompilerSelfShiftTail] permits the same finite tree to
  be compiled over an arbitrary self-shifting tail.  A witnessed PA-axiom
  context supplies precisely that tail invariant.

  The ordinary proof may itself use a finite list of PA axioms.  Those axioms
  are not silently weakened into the old context: their standard witnesses
  are prepended in lockstep by [RawCodedPAAxiomWitnessPrefix].  The resulting
  local root and the resulting witness traversal therefore mention literally
  the same context code.  This is the form needed when a dynamic successor
  compiler adds a fixed PA helper theorem to its current common context.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  BoundedConsistency
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedPAAxiomWitnessPrefix.

Import ListNotations.

Module PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedConsistency.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedPAAxiomWitnessPrefix.

(** Agreement on ordinary PA formulae identifies the template context prefix
    with the synchronized quoted-axiom prefix.  This equality is important:
    merely proving that the two contexts contain the same formulae would not
    suffice, because every raw proof-node code stores its literal context. *)
Lemma raw_templateContextCodeOnTail_embedPAAxiomWitnesses : forall
    (M : RawPAModel)
      (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses baseContext,
  rawTemplateContextCodeOnTail translation baseContext
    (embedPAContext (map witnessedAxiom witnesses)) =
  rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext.
Proof.
  intros M translation hagreement witnesses.
  induction witnesses as [| witness tail ih]; intro baseContext.
  - reflexivity.
  - change
      (rawListNode M
        (rawTemplateFormula translation
          (embedPAFormula (witnessedAxiom witness)))
        (rawTemplateContextCodeOnTail translation baseContext
          (embedPAContext (map witnessedAxiom tail))) =
       rawListNode M
        (rawQuotedFormulaCode M (witnessedAxiom witness))
        (rawStandardPAAxiomWitnessPrefixContextCode
          M tail baseContext)).
    rewrite (rawTemplateFormula_embedPA hagreement
      (witnessedAxiom witness)).
    rewrite ih. reflexivity.
Qed.

(** Compile one explicit ordinary proof over an arbitrary witnessed tail.
    The returned prefix witness code and proof context are synchronized by
    construction, while the proof root is the transparent template tree
    emitted over that exact tail. *)
Theorem raw_codedTemplatePALocalProofOf_on_witnessed_tail : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext witnesses derivation,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawProofValid derivation ->
  rawContext derivation = map witnessedAxiom witnesses ->
  exists root : M,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation
        (embedPAFormula (rawConclusion derivation))) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext witnesses derivation
    hbase hvalid hcontext.
  set (root := rawTemplateProofCodeOnTail translation baseContext
    (embedRawProof derivation)).
  exists root. split.
  - exact (raw_codedPAAxiomWitnessContext_standardPrefix
      M hPA witnesses baseWitnessList baseContext hbase).
  - pose proof
      (raw_templateProofOnPAAxiomContext_localProof
        M hPA translation baseWitnessList baseContext
        (embedRawProof derivation) hbase
        (embedRawProof_valid derivation hvalid)) as hproof.
    rewrite embedRawProof_context in hproof.
    rewrite hcontext in hproof.
    rewrite (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
      M translation hagreement witnesses baseContext) in hproof.
    rewrite embedRawProof_conclusion in hproof.
    exact hproof.
Qed.

(** Public fixed-theorem endpoint.  Completeness of the finite ordinary proof
    tree selects a metatheoretic witness prefix; the theorem above then emits
    a local proof over the caller's existing witnessed PA base.  The target
    formula may still contain opaque carrier parameters through
    [translation], even though the source theorem is ordinary PA syntax. *)
Theorem raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail : forall
    (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext phi,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  Formula.BProv Formula.Ax_s [] phi ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation (embedPAFormula phi)) root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext phi hbase
    (axioms & haxioms & hprov).
  rewrite app_nil_r in hprov.
  destruct (Ax_s_list_has_witnesses axioms haxioms)
    as [witnesses hwitnesses].
  rewrite <- hwitnesses in hprov.
  destruct (ProvTree_complete _ _ hprov) as [derivation _].
  set (rawDerivation := rawOfProvTree derivation).
  assert (hrawValid : RawProofValid rawDerivation).
  {
    unfold rawDerivation.
    exact (RawProofValid_rawOfProvTree
      (map witnessedAxiom witnesses) phi derivation).
  }
  assert (hrawContext : rawContext rawDerivation =
      map witnessedAxiom witnesses).
  {
    unfold rawDerivation.
    rewrite rawOfProvTree_context. reflexivity.
  }
  destruct (raw_codedTemplatePALocalProofOf_on_witnessed_tail
    M hPA translation hagreement baseWitnessList baseContext
    witnesses rawDerivation hbase hrawValid hrawContext)
    as [root [hwitnessed hproof]].
  exists witnesses, root. split; [exact hwitnessed |].
  unfold rawDerivation in hproof.
  rewrite rawOfProvTree_conclusion in hproof.
  exact hproof.
Qed.

End PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
