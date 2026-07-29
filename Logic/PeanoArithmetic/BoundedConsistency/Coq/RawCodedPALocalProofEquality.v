(** Local-proof wrappers for represented equality elimination. *)

From Stdlib Require Import List.
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
  RawCodedTemplateParameterAbstraction
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
Import PABoundedRawCodedTemplateParameterAbstraction.
Import PABoundedRawCodedTemplateProofCompiler.

Import ListNotations.

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

(** Replace one named parameter using an equality oriented from the desired
    replacement to that parameter.  Equality symmetry and elimination both
    occur in the represented calculus.  Parameter abstraction supplies the
    capture-avoiding one-variable motive, and its round trip identifies the
    already-proved source instance literally with [input]. *)
Theorem
    raw_codedPALocalProofOf_templateParameterTransport_reverse : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context name replacement input equalityRoot inputRoot,
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (tfEq replacement (ttParameter name))) equalityRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation input) inputRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation
        (templateFormulaOpen replacement
          (templateFormulaAbstractParameter name input))) root.
Proof.
  intros M hPA translation context name replacement input
    equalityRoot inputRoot hequality hinput.
  destruct
    (raw_codedPALocalProofOf_templateEqSymmetry
      M hPA translation context replacement (ttParameter name)
      equalityRoot hequality)
    as [symmetryRoot hsymmetry].
  pose proof
    (raw_codedPALocalProofOf_templateEqElim
      M hPA translation context
      (ttParameter name) replacement
      (templateFormulaAbstractParameter name input)
      symmetryRoot inputRoot hsymmetry) as htransport.
  rewrite templateFormulaAbstractParameter_open in htransport.
  specialize (htransport hinput).
  eexists. exact htransport.
Qed.

(** Capture-avoiding replacement of any finite sequence of named template
    parameters.  Bindings are applied from left to right, matching the order
    in which the represented equality roots are consumed. *)
Fixpoint templateFormulaReplaceParameters
    (bindings : list (TemplateParameterName * TemplateTerm))
    (input : TemplateFormula) : TemplateFormula :=
  match bindings with
  | [] => input
  | (name, replacement) :: remaining =>
      templateFormulaReplaceParameters remaining
        (templateFormulaOpen replacement
          (templateFormulaAbstractParameter name input))
  end.

(** Transparent normal form for the same ordered finite replacement.  This
    form is intended for concrete syntax calculations: unlike the
    proof-producing abstract/open spelling, it reduces structurally through
    the target formula. *)
Fixpoint templateFormulaReplaceParametersDirect
    (bindings : list (TemplateParameterName * TemplateTerm))
    (input : TemplateFormula) : TemplateFormula :=
  match bindings with
  | [] => input
  | (name, replacement) :: remaining =>
      templateFormulaReplaceParametersDirect remaining
        (templateFormulaReplaceParameter name replacement input)
  end.

Theorem templateFormulaReplaceParameters_eq_direct : forall bindings input,
  templateFormulaReplaceParameters bindings input =
  templateFormulaReplaceParametersDirect bindings input.
Proof.
  induction bindings as [|[name replacement] remaining ih]; intro input.
  - reflexivity.
  - cbn [templateFormulaReplaceParameters
      templateFormulaReplaceParametersDirect].
    rewrite templateFormulaAbstractParameter_open_as_replace.
    apply ih.
Qed.

(** Iterate reverse parameter transport for an arbitrary finite family.
    Every equality root and every intermediate proof remains in one literal
    context; no adequacy, freshness, or context-extension hypothesis is
    needed by equality elimination itself. *)
Theorem
    raw_codedPALocalProofOf_templateParameterTransports_reverse : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context bindings equalityRoots input inputRoot,
  Forall2
    (fun binding equalityRoot =>
      RawCodedPALocalProofOf M context
        (rawTemplateFormula translation
          (tfEq (snd binding) (ttParameter (fst binding)))) equalityRoot)
    bindings equalityRoots ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation input) inputRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation
        (templateFormulaReplaceParameters bindings input)) root.
Proof.
  intros M hPA translation context bindings equalityRoots
    input inputRoot hequalities hinput.
  revert input inputRoot hinput.
  induction hequalities as
      [|binding equalityRoot remainingBindings remainingRoots
        hequality hequalities ih];
    intros input inputRoot hinput.
  - exists inputRoot. exact hinput.
  - destruct binding as [name replacement].
    cbn [fst snd templateFormulaReplaceParameters] in hequality |- *.
    destruct
      (raw_codedPALocalProofOf_templateParameterTransport_reverse
        M hPA translation context name replacement input
        equalityRoot inputRoot hequality hinput)
      as [transportedRoot htransported].
    exact (ih _ transportedRoot htransported).
Qed.

End PABoundedRawCodedPALocalProofEquality.
