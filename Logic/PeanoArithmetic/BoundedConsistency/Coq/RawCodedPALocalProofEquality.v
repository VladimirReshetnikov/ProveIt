(** Local-proof wrappers for represented equality elimination. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedProofEqElimConstructor
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler.

Module PABoundedRawCodedPALocalProofEquality.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofEqElimConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.

(** Transport a represented motive along a represented equality.  The body
    and both substitution traces remain arbitrary carrier data; no formula
    is decoded and no syntactic adequacy hypothesis is needed. *)
Theorem raw_codedPALocalProofOf_eqElim : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    context source target body sourceInstance targetInstance
    equalityRoot bodyRoot,
  RawCodedPALocalProofOf M context
    (rawFormulaEqCode M source target) equalityRoot ->
  RawCodedFormulaSingleSubstitution M source body sourceInstance ->
  RawCodedPALocalProofOf M context sourceInstance bodyRoot ->
  RawCodedFormulaSingleSubstitution M target body targetInstance ->
  RawCodedPALocalProofOf M context targetInstance
    (rawProofEqElimRoot M context source target body
      equalityRoot bodyRoot).
Proof.
  intros M hPA context source target body sourceInstance targetInstance
    equalityRoot bodyRoot
    [hequalityCoverage hequalityEndpoint]
    hsourceSubstitution [hbodyCoverage hbodyEndpoint]
    htargetSubstitution.
  split.
  - exact (raw_proofEqElim_ruleCoverage M hPA
      context source target body sourceInstance equalityRoot bodyRoot
      hequalityCoverage hequalityEndpoint hsourceSubstitution
      hbodyCoverage hbodyEndpoint).
  - exact (raw_proofEqElim_endpoint M
      context source target body targetInstance
      equalityRoot bodyRoot htargetSubstitution).
Qed.

(** Translation-generic template specialization.  The translation record
    supplies both represented substitution traces, so clients mention only
    the equality and the motive instance they already proved. *)
Theorem raw_codedPALocalProofOf_templateEqElim : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context source target motive equalityRoot motiveRoot,
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation (tfEq source target)) equalityRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateFormulaOpen source motive)) motiveRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateFormulaOpen target motive))
    (rawProofEqElimRoot M context
      (rawTemplateTerm translation source)
      (rawTemplateTerm translation target)
      (rawTemplateFormula translation motive)
      equalityRoot motiveRoot).
Proof.
  intros M hPA translation context source target motive
    equalityRoot motiveRoot hequality hmotive.
  rewrite rawTemplateFormula_eq in hequality.
  exact (raw_codedPALocalProofOf_eqElim M hPA context
    (rawTemplateTerm translation source)
    (rawTemplateTerm translation target)
    (rawTemplateFormula translation motive)
    (rawTemplateFormula translation
      (templateFormulaOpen source motive))
    (rawTemplateFormula translation
      (templateFormulaOpen target motive))
    equalityRoot motiveRoot hequality
    (rawTemplateFormula_open translation motive source)
    hmotive
    (rawTemplateFormula_open translation motive target)).
Qed.

End PABoundedRawCodedPALocalProofEquality.
