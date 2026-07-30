(** Compile both orientations of zero/one distinctness in one extension. *)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofStandardWitnessTailTransport.

Module PABoundedRawCodedZeroOneDistinctnessProofCompilation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.

Definition zeroEqualsOneFormula : formula :=
  pEq tZero (Term.numeral 1).

Definition oneEqualsZeroFormula : formula :=
  pEq (Term.numeral 1) tZero.

Definition zeroNotOneFormula : formula :=
  pImp zeroEqualsOneFormula pBot.

Definition oneNotZeroFormula : formula :=
  pImp oneEqualsZeroFormula pBot.

Definition zeroOneDistinctnessPairFormula : formula :=
  pAnd zeroNotOneFormula oneNotZeroFormula.

(** The right orientation is PA's zero-not-successor axiom instance.  The
    left orientation uses equality symmetry under its temporary assumption. *)
Lemma BProv_Ax_s_zeroOneDistinctnessPair :
  Formula.BProv Formula.Ax_s [] zeroOneDistinctnessPairFormula.
Proof.
  unfold zeroOneDistinctnessPairFormula.
  apply Formula.BProv_andI.
  - unfold zeroNotOneFormula, zeroEqualsOneFormula.
    apply Formula.BProv_impI.
    assert (heq : Formula.BProv Formula.Ax_s
        [pEq tZero (Term.numeral 1)]
        (pEq (Term.numeral 1) tZero)).
    {
      apply Formula.BProv_eqSym.
      apply Formula.BProv_ass_head.
    }
    exact (Formula.BProv_mp Formula.Ax_s
      [pEq tZero (Term.numeral 1)]
      (pEq (Term.numeral 1) tZero) pBot
      (Formula.BProv_Ax_s_zeroNotSucc_term
        [pEq tZero (Term.numeral 1)] tZero) heq).
  - unfold oneNotZeroFormula, oneEqualsZeroFormula.
    exact (Formula.BProv_Ax_s_zeroNotSucc_term [] tZero).
Qed.

(** Both projected contradiction roots share one helper-witness extension.
    Retaining inclusion of the caller's context lets later growing traversal
    compilers transport their already constructed row-choice proof exactly
    once. *)
Theorem raw_codedZeroOneDistinctness_roots_on_witnessed_extension : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists witnesses leftRoot rightRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawContextListIncluded M baseContext
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation
        (embedPAFormula zeroNotOneFormula)) leftRoot /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation
        (embedPAFormula oneNotZeroFormula)) rightRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext hbase.
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      zeroOneDistinctnessPairFormula hbase
      BProv_Ax_s_zeroOneDistinctnessPair)
    as (witnesses & pairRoot & hextended & hpair).
  unfold zeroOneDistinctnessPairFormula in hpair.
  change (RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawTemplateFormula translation
      (tfAnd (embedPAFormula zeroNotOneFormula)
        (embedPAFormula oneNotZeroFormula))) pairRoot) in hpair.
  rewrite rawTemplateFormula_and in hpair.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawTemplateFormula translation (embedPAFormula zeroNotOneFormula))
    (rawTemplateFormula translation (embedPAFormula oneNotZeroFormula))
    pairRoot hpair) as hleft.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawTemplateFormula translation (embedPAFormula zeroNotOneFormula))
    (rawTemplateFormula translation (embedPAFormula oneNotZeroFormula))
    pairRoot hpair) as hright.
  lazymatch type of hleft with
  | RawCodedPALocalProofOf _ _ _ ?leftRoot =>
      lazymatch type of hright with
      | RawCodedPALocalProofOf _ _ _ ?rightRoot =>
          exists witnesses, leftRoot, rightRoot;
          split; [exact hextended |];
          split;
          [ exact (raw_standardPAAxiomWitnessPrefixContextCode_target_included
              M hPA witnesses baseContext)
          | split; assumption ]
      end
  end.
Qed.

End PABoundedRawCodedZeroOneDistinctnessProofCompilation.
