(**
  Represented use of assignment prefix-definedness at one smaller index.

  [RawCodedAssignment] proves in ordinary PA that

      DefinedThrough(code, step, bound) ->
      idx < bound ->
      exists value, Lookup(code, step, idx, value).

  The fixed PA proof may require a finite standard axiom witness prefix.
  This module compiles it over an arbitrary already-witnessed tail and
  transports both caller-supplied premises through exactly that same prefix
  before applying represented modus ponens twice.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedProofBinaryConstructors
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail.

Module PABoundedRawCodedAssignmentDefinedThroughProofCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.

(** The output retains the explicit standard prefix because later compilers
    may need to transport additional roots into this same enlarged context. *)
Theorem
    raw_codedPALocalProofOf_assignmentDefinedThrough_entry_of_lt_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext code step bound index
      definedRoot ltRoot,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation
      (embedPAFormula
        (codedAssignmentDefinedThroughTermAt code step bound)))
    definedRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation
      (embedPAFormula (Formula.ltTermAt index bound))) ltRoot ->
  exists (prefix : StandardPAAxiomWitnessPrefix) entryRoot,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        prefix baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
      (rawTemplateFormula translation
        (embedPAFormula (betaEntryExistsTermAt code step index)))
      entryRoot.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    code step bound index definedRoot ltRoot
    hbase hdefined hlt.
  destruct
    (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext
      (pImp (codedAssignmentDefinedThroughTermAt code step bound)
        (pImp (Formula.ltTermAt index bound)
          (betaEntryExistsTermAt code step index)))
      hbase
      (BProv_Ax_s_codedAssignmentDefinedThrough_entry_imp
        code step bound index))
    as (prefix & implicationRoot & hprefixed & himplication).
  pose proof
    (raw_codedPAAxiomWitnessPrefix_context_realizable_of_witnessed
      M baseWitnessList baseContext hbase) as hbaseRealizable.
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA prefix baseContext
    (rawTemplateFormula translation
      (embedPAFormula
        (codedAssignmentDefinedThroughTermAt code step bound)))
    definedRoot hbaseRealizable hdefined)
    as [prefixedDefinedRoot hprefixedDefined].
  destruct (raw_codedPALocalProofOf_standardPAAxiomWitnessPrefix
    M hPA prefix baseContext
    (rawTemplateFormula translation
      (embedPAFormula (Formula.ltTermAt index bound)))
    ltRoot hbaseRealizable hlt)
    as [prefixedLtRoot hprefixedLt].
  (* Expose the two PA implication constructors as template constructors.
     The compiler preserves the embedded conclusion syntactically, but Rocq
     does not unfold the recursive embedding deeply enough for the generic
     [rawTemplateFormula_imp] rewrite to find either constructor on its own. *)
  change (RawCodedPALocalProofOf M
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
    (rawTemplateFormula translation
      (tfImp
        (embedPAFormula
          (codedAssignmentDefinedThroughTermAt code step bound))
        (tfImp
          (embedPAFormula (Formula.ltTermAt index bound))
          (embedPAFormula
            (betaEntryExistsTermAt code step index)))))
    implicationRoot) in himplication.
  rewrite !rawTemplateFormula_imp in himplication.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
    (rawTemplateFormula translation
      (embedPAFormula
        (codedAssignmentDefinedThroughTermAt code step bound)))
    _
    implicationRoot prefixedDefinedRoot himplication hprefixedDefined)
    as hafterDefined.
  lazymatch type of hafterDefined with
  | RawCodedPALocalProofOf _ _ _ ?afterDefinedRoot =>
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
        (rawTemplateFormula translation
          (embedPAFormula (Formula.ltTermAt index bound)))
        (rawTemplateFormula translation
          (embedPAFormula (betaEntryExistsTermAt code step index)))
        afterDefinedRoot prefixedLtRoot hafterDefined hprefixedLt)
        as hentry;
      exists prefix,
        (rawProofImpERoot M
          (rawStandardPAAxiomWitnessPrefixContextCode M prefix baseContext)
          (rawTemplateFormula translation
            (embedPAFormula (Formula.ltTermAt index bound)))
          (rawTemplateFormula translation
            (embedPAFormula (betaEntryExistsTermAt code step index)))
          afterDefinedRoot prefixedLtRoot);
      split; [exact hprefixed | exact hentry]
  end.
Qed.

End PABoundedRawCodedAssignmentDefinedThroughProofCompilation.
