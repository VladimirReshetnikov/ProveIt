(**
  Finite existential introduction in an arbitrary local proof context.

  A traversal certificate commonly chooses a fixed tuple of witnesses and
  proves only the fully opened body.  This module packages the repeated
  [Ex-I] construction independently of any particular tuple length.  The
  opening function is partial on purpose: a successful result records that
  every requested witness met a literal leading existential binder.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedProofExIConstructor
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler.

Module PABoundedRawCodedPALocalProofExistentialIntroductionChain.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedProofExIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.

(** Open one leading existential for each witness, from the outermost binder
    inward.  Returning [None] instead of a fallback formula prevents clients
    from accidentally proving a malformed binder prefix. *)
Fixpoint templateExistentialOpenMany
    (source : TemplateFormula) (witnesses : list TemplateTerm)
    : option TemplateFormula :=
  match witnesses with
  | [] => Some source
  | witness :: remaining =>
      match source with
      | tfEx body =>
          templateExistentialOpenMany
            (templateFormulaOpen witness body) remaining
      | _ => None
      end
  end.

(** One represented existential introduction over any literal context.  The
    structural template translation supplies the exact single-substitution
    trace required by the raw proof constructor. *)
Theorem raw_codedPALocalProofOf_templateExI : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context body witness child,
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateFormulaOpen witness body)) child ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation (tfEx body))
    (rawProofExIRoot M context
      (rawTemplateFormula translation body)
      (rawTemplateTerm translation witness) child).
Proof.
  intros M hPA translation context body witness child
    [hcoverage hendpoint].
  split.
  - apply (raw_proofExI_ruleCoverage M hPA context
      (rawTemplateFormula translation body)
      (rawTemplateTerm translation witness)
      (rawTemplateFormula translation
        (templateFormulaOpen witness body)) child).
    + exact (rawTemplateFormula_open translation body witness).
    + exact hcoverage.
    + exact hendpoint.
  - rewrite rawTemplateFormula_ex.
    apply raw_proofExI_endpoint.
Qed.

(** Rebuild all requested existential binders.  Proof roots are existentially
    hidden because downstream compilers care about the endpoint and coverage,
    not the nested pairing code selected by this implementation. *)
Theorem raw_codedPALocalProofOf_templateExistentialOpenMany : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context source witnesses target child,
  templateExistentialOpenMany source witnesses = Some target ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation target) child ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation source) root.
Proof.
  intros M hPA translation context source witnesses.
  revert source.
  induction witnesses as [|witness remaining ih];
    intros source target child hopen htarget.
  - cbn [templateExistentialOpenMany] in hopen.
    inversion hopen; subst target.
    exists child. exact htarget.
  - destruct source; try discriminate hopen.
    cbn [templateExistentialOpenMany] in hopen.
    destruct (ih (templateFormulaOpen witness source)
      target child hopen htarget) as [innerRoot hinner].
    exists (rawProofExIRoot M context
      (rawTemplateFormula translation source)
      (rawTemplateTerm translation witness) innerRoot).
    exact (raw_codedPALocalProofOf_templateExI M hPA translation
      context source witness innerRoot hinner).
Qed.

End PABoundedRawCodedPALocalProofExistentialIntroductionChain.
