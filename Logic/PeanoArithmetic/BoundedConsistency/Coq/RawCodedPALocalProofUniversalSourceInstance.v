(**
  Generic compilation of a universal PA theorem at a carrier-valued term.

  A metatheoretic PA derivation is first realized over a finite witnessed
  axiom extension of the caller's base.  Represented All-E then substitutes
  an arbitrary model term into its body.  Finally, a finite direct-template
  context is inserted above the instantiated proof.  This is the common
  proof-code pattern used by the dynamic reroot and opened-coverage sources.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofAllEConstructor
  RawCodedContextStructure
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalElimination
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedPAAxiomWitness
  RawCodedPAAxiomWitnessPrefix
  RawCodedRestrictedPAProof
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateDirectStructuralPAAgreement
  RawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.

Import ListNotations.

Module PABoundedRawCodedPALocalProofUniversalSourceInstance.

Import PA.
Import PABoundedCodedProof.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalElimination.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralPAAgreement.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectOrIntroductionLeftDynamicRerootCompilation.

(** No syntax of the source body, replacement, target, or inserted prefix is
    inspected here.  Their only connection is the represented single-
    substitution trace supplied by the caller. *)
Theorem raw_codedPALocalProof_universalSourceInstance_under_directPrefix :
  forall (M : RawPAModel) (hPA : RawPASatisfies M), forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    baseWitnessList baseContext sourceBody replacement instance prefix,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  Formula.BProv Formula.Ax_s [] (pAll sourceBody) ->
  RawCodedFormulaSingleSubstitution M replacement
    (rawQuotedFormulaCode M sourceBody) instance ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail
        (rawDirectStructuralTemplateTranslation M hPA inputs)
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses baseContext)
        prefix)
      instance root.
Proof.
  intros M hPA inputs baseWitnessList baseContext sourceBody
    replacement instance prefix hbase hsourceTheorem hsubstitution.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  destruct (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation
    (rawDirectStructuralTemplatePAAgreement M hPA inputs)
    baseWitnessList baseContext (pAll sourceBody)
    hbase hsourceTheorem)
    as (witnesses & sourceRoot & hextended & hsource).
  set (extendedContext :=
    rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext).

  assert (hall : RawCodedPALocalProofOf M extendedContext
      (rawFormulaAllCode M (rawQuotedFormulaCode M sourceBody))
      sourceRoot).
  {
    unfold extendedContext, translation in *.
    change (RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
      (rawQuotedFormulaCode M (pAll sourceBody)) sourceRoot).
    rewrite <- (rawTemplateFormula_embedPA
      (rawDirectStructuralTemplatePAAgreement M hPA inputs)
      (pAll sourceBody)).
    exact hsource.
  }
  pose proof (raw_codedPALocalProofOf_allE M hPA extendedContext
    (rawQuotedFormulaCode M sourceBody)
    replacement instance sourceRoot hall hsubstitution) as hinstance.
  destruct (raw_codedPALocalProof_directTemplatePrefix M hPA inputs
    extendedContext prefix instance
    (rawProofAllERoot M extendedContext
      (rawQuotedFormulaCode M sourceBody) replacement sourceRoot)
    (raw_codedPAAxiomWitnessContext_context_realizable M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      extendedContext hextended)
    hinstance) as [root hroot].
  exists witnesses, root. split; assumption.
Qed.

End PABoundedRawCodedPALocalProofUniversalSourceInstance.
