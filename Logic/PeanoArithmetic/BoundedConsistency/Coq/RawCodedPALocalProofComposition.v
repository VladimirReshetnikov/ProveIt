(**
  Propositional composition in an arbitrary model-coded proof context.

  [RawCodedPAOpenProofComposition] already supplies implication and bottom
  elimination when the context has the distinguished shape

      assumption :: witnessed-PA-context.

  After the three existential eliminations used by the restricted-
  consistency compiler, however, the context contains several temporary
  assumptions.  The smaller [RawCodedPALocalProofOf] package is the right
  interface there.  The two constructors below deliberately retain the
  context verbatim and merely put the corresponding honest raw proof node
  over already covered children.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofEndpoints
  RawCodedProofRuleCoverage RawCodedProofUnaryConstructors
  RawCodedProofBinaryConstructors RawCodedPALocalProofExistential
  RawCodedTemplateSyntax RawCodedTemplateProofCompiler.

Module PABoundedRawCodedPALocalProofComposition.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.

(** Bottom elimination does not inspect the temporary context. *)
Theorem raw_codedPALocalProofOf_botE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context child,
  RawCodedPALocalProofOf M context (rawFormulaBotCode M) child ->
  forall target,
  RawCodedPALocalProofOf M context target
    (rawProofBotERoot M context target child).
Proof.
  intros M hPA context child [hcoverage hendpoint] target.
  split.
  - exact (raw_proofBotE_ruleCoverage M hPA
      context target child hcoverage hendpoint).
  - exact (raw_proofBotE_endpoint M context target child).
Qed.

(** Modus ponens for two local proofs sharing exactly the same context. *)
Theorem raw_codedPALocalProofOf_impE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context antecedent consequent impChild antecedentChild,
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M antecedent consequent) impChild ->
  RawCodedPALocalProofOf M context antecedent antecedentChild ->
  RawCodedPALocalProofOf M context consequent
    (rawProofImpERoot M context antecedent consequent
      impChild antecedentChild).
Proof.
  intros M hPA context antecedent consequent impChild antecedentChild
    [himpCoverage himpEndpoint]
    [hantecedentCoverage hantecedentEndpoint].
  split.
  - exact (raw_proofImpE_ruleCoverage M hPA
      context antecedent consequent impChild antecedentChild
      himpCoverage himpEndpoint
      hantecedentCoverage hantecedentEndpoint).
  - exact (raw_proofImpE_endpoint M
      context antecedent consequent impChild antecedentChild).
Qed.

(** Three successive modus-ponens steps in one unchanged local context.  The
    existential endpoint avoids exposing the nested binary proof-root term. *)
Corollary raw_codedPALocalProofOf_impE3 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context first second third conclusion
      implicationRoot firstRoot secondRoot thirdRoot,
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M first
      (rawFormulaImpCode M second
        (rawFormulaImpCode M third conclusion))) implicationRoot ->
  RawCodedPALocalProofOf M context first firstRoot ->
  RawCodedPALocalProofOf M context second secondRoot ->
  RawCodedPALocalProofOf M context third thirdRoot ->
  exists root, RawCodedPALocalProofOf M context conclusion root.
Proof.
  intros M hPA context first second third conclusion
    implicationRoot firstRoot secondRoot thirdRoot
    himp hfirst hsecond hthird.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    first (rawFormulaImpCode M second
      (rawFormulaImpCode M third conclusion))
    implicationRoot firstRoot himp hfirst) as himp2.
  lazymatch type of himp2 with
  | RawCodedPALocalProofOf _ _ _ ?imp2Root =>
      pose proof (raw_codedPALocalProofOf_impE M hPA context
        second (rawFormulaImpCode M third conclusion)
        imp2Root secondRoot himp2 hsecond) as himp3
  end.
  lazymatch type of himp3 with
  | RawCodedPALocalProofOf _ _ _ ?imp3Root =>
      exists (rawProofImpERoot M context third conclusion
        imp3Root thirdRoot);
      exact (raw_codedPALocalProofOf_impE M hPA context
        third conclusion imp3Root thirdRoot himp3 hthird)
  end.
Qed.

(** Safe structural views of a fixed template implication.  Their fallback is
    irrelevant whenever [TemplateImp3Shape] has been audited. *)
Definition templateImpAntecedent (source : TemplateFormula)
    : TemplateFormula :=
  match source with
  | tfImp antecedent _ => antecedent
  | _ => tfBot
  end.

Definition templateImpConsequent (source : TemplateFormula)
    : TemplateFormula :=
  match source with
  | tfImp _ consequent => consequent
  | _ => tfBot
  end.

Definition TemplateImp3Shape (source : TemplateFormula) : Prop :=
  source = tfImp
    (templateImpAntecedent source)
    (tfImp
      (templateImpAntecedent (templateImpConsequent source))
      (tfImp
        (templateImpAntecedent
          (templateImpConsequent (templateImpConsequent source)))
        (templateImpConsequent
          (templateImpConsequent (templateImpConsequent source))))).

Arguments TemplateImp3Shape source : clear implicits.

(** Template-facing form of the three-premise implication chain. *)
Theorem raw_codedPALocalProofOf_templateImpE3 : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context source implicationRoot firstRoot secondRoot thirdRoot,
  TemplateImp3Shape source ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation source) implicationRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImpAntecedent source)) firstRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImpAntecedent (templateImpConsequent source))) secondRoot ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateImpAntecedent
        (templateImpConsequent (templateImpConsequent source)))) thirdRoot ->
  exists root,
    RawCodedPALocalProofOf M context
      (rawTemplateFormula translation
        (templateImpConsequent
          (templateImpConsequent (templateImpConsequent source)))) root.
Proof.
  intros M hPA translation context source
    implicationRoot firstRoot secondRoot thirdRoot hshape
    himp hfirst hsecond hthird.
  rewrite hshape, !rawTemplateFormula_imp in himp.
  exact (raw_codedPALocalProofOf_impE3 M hPA context
    (rawTemplateFormula translation (templateImpAntecedent source))
    (rawTemplateFormula translation
      (templateImpAntecedent (templateImpConsequent source)))
    (rawTemplateFormula translation
      (templateImpAntecedent
        (templateImpConsequent (templateImpConsequent source))))
    (rawTemplateFormula translation
      (templateImpConsequent
        (templateImpConsequent (templateImpConsequent source))))
    implicationRoot firstRoot secondRoot thirdRoot
    himp hfirst hsecond hthird).
Qed.

End PABoundedRawCodedPALocalProofComposition.
