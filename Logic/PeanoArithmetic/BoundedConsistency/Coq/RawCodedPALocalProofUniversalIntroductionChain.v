(**
  Repeated universal introduction in an arbitrary translated local context.

  A traversal row has five leading universal binders.  Its body proof lives
  in the context obtained by shifting every temporary assumption five times,
  and each represented [AllI] node removes one of those context shifts.  This
  module packages that finite bookkeeping independently of any particular
  traversal or formula.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPALocalProofExistential
  RawCodedProofAllIConstructor
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler.

Module PABoundedRawCodedPALocalProofUniversalIntroductionChain.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.

(** Iterate the eigenvariable context shift from the outside inward. *)
Fixpoint templateContextShiftMany
    (count : nat) (context : TemplateContext) : TemplateContext :=
  match count with
  | 0 => context
  | S smaller =>
      templateContextShiftMany smaller (templateContextShift context)
  end.

(** The matching right-nested universal prefix. *)
Fixpoint templateFormulaAllMany
    (count : nat) (body : TemplateFormula) : TemplateFormula :=
  match count with
  | 0 => body
  | S smaller => tfAll (templateFormulaAllMany smaller body)
  end.

(** Rebuild all represented [AllI] roots.  The proof uses only the exact
    represented context-shift trace already supplied by the template
    translation; it requires no closure or self-shift hypothesis. *)
Theorem raw_codedPALocalProofOf_universal_introduction_chain : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    count context body deepRoot,
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (templateContextShiftMany count context))
    (rawTemplateFormula translation body) deepRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        (templateFormulaAllMany count body)) root.
Proof.
  intros M hPA translation count.
  induction count as [|smaller ih];
    intros context body deepRoot hdeep.
  - exists deepRoot. exact hdeep.
  - cbn [templateContextShiftMany templateFormulaAllMany] in hdeep |- *.
    destruct (ih (templateContextShift context) body deepRoot hdeep)
      as [innerRoot hinner].
    destruct hinner as [hinnerCoverage hinnerEndpoint].
    exists (rawProofAllIRoot M
      (rawTemplateContextCode translation context)
      (rawTemplateFormula translation
        (templateFormulaAllMany smaller body)) innerRoot).
    split.
    + exact (raw_proofAllI_ruleCoverage M hPA
        (rawTemplateContextCode translation context)
        (rawTemplateContextCode translation (templateContextShift context))
        (rawTemplateFormula translation
          (templateFormulaAllMany smaller body)) innerRoot
        (raw_templateContext_shift M hPA translation context)
        hinnerCoverage hinnerEndpoint).
    + rewrite rawTemplateFormula_all.
      exact (raw_proofAllI_endpoint M
        (rawTemplateContextCode translation context)
        (rawTemplateFormula translation
          (templateFormulaAllMany smaller body)) innerRoot).
Qed.

End PABoundedRawCodedPALocalProofUniversalIntroductionChain.
