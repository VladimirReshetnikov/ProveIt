(** Local-proof wrappers for represented equality elimination. *)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedProofEqReflConstructor
  RawCodedProofEqElimConstructor
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateRenamingSubstitution
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
Import PABoundedRawCodedProofEqReflConstructor.
Import PABoundedRawCodedProofEqElimConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateRenamingSubstitution.
Import PABoundedRawCodedTemplateProofCompiler.

(** Premise-free represented equality reflexivity. *)
Theorem raw_codedPALocalProofOf_eqRefl : forall
    (M : RawPAModel), RawPASatisfies M -> forall context witness,
  RawCodedPALocalProofOf M context
    (rawFormulaEqCode M witness witness)
    (rawProofEqReflRoot M context witness).
Proof.
  intros M hPA context witness.
  split.
  - exact (raw_proofEqRefl_ruleCoverage M hPA context witness).
  - exact (raw_proofEqRefl_endpoint M context witness).
Qed.

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

(** A one-variable motive whose opening states that its replacement equals a
    fixed outer term.  Shifting the fixed term protects its free variables
    from the motive binder. *)
Definition templateEqualitySymmetryMotive
    (source : TemplateTerm) : TemplateFormula :=
  tfEq (ttVar 0) (templateTermRename S source).

Lemma templateEqualitySymmetryMotive_open : forall source replacement,
  templateFormulaOpen replacement
    (templateEqualitySymmetryMotive source) =
  tfEq replacement source.
Proof.
  intros source replacement.
  unfold templateEqualitySymmetryMotive, templateFormulaOpen.
  cbn [templateFormulaSubst].
  rewrite templateTermSubst_rename.
  transitivity
    (tfEq replacement
      (templateTermSubst (fun index => ttVar index) source)).
  - apply f_equal. apply templateTermSubst_ext.
    intro index. reflexivity.
  - rewrite templateTermSubst_id. reflexivity.
Qed.

(** Symmetry derived inside the represented proof calculus from reflexivity
    and the generic template equality eliminator. *)
Theorem raw_codedPALocalProofOf_templateEqSymmetry : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context source target equalityRoot,
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation (tfEq source target)) equalityRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation (tfEq target source)) root.
Proof.
  intros M hPA translation context source target equalityRoot hequality.
  pose proof (raw_codedPALocalProofOf_eqRefl M hPA context
    (rawTemplateTerm translation source)) as hrefl.
  assert (hreflTemplate : RawCodedPALocalProofOf M context
      (rawTemplateFormula translation (tfEq source source))
      (rawProofEqReflRoot M context
        (rawTemplateTerm translation source))).
  {
    rewrite rawTemplateFormula_eq.
    exact hrefl.
  }
  pose proof (raw_codedPALocalProofOf_templateEqElim M hPA translation
    context source target (templateEqualitySymmetryMotive source)
    equalityRoot
    (rawProofEqReflRoot M context
      (rawTemplateTerm translation source))
    hequality) as htransport.
  rewrite templateEqualitySymmetryMotive_open in htransport.
  specialize (htransport hreflTemplate).
  rewrite templateEqualitySymmetryMotive_open in htransport.
  eexists. exact htransport.
Qed.

End PABoundedRawCodedPALocalProofEquality.
