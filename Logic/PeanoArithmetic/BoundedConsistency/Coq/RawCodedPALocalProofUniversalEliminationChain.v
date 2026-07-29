(**
  Finite chains of represented universal elimination.

  Several PA-internal construction theorems are universally closed over a
  fixed finite tuple of codes.  Their clients previously had to repeat the
  same [allE] proof-root assembly once per component.  This module packages
  the operation traces as a small inductive relation and compiles the whole
  chain while preserving one literal model-coded proof context.

  The second theorem composes that compiler with the existing witnessed-tail
  realization of an arbitrary fixed PA theorem.  Thus a caller supplies only
  the represented substitution chain from the theorem's quoted source to its
  desired carrier-valued instance; the finite PA-axiom prefix and every proof
  root are constructed internally.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofAllEConstructor
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedPALocalProofUniversalElimination
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail.

Module PABoundedRawCodedPALocalProofUniversalEliminationChain.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofUniversalElimination.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.

(** A cons step records exactly the substitution checked by one represented
    universal-elimination node.  The intermediate [instance] becomes the
    source of the remaining chain, so no functionality or independently
    chosen formula-operation trace is required. *)
Inductive RawCodedUniversalEliminationChain (M : RawPAModel) :
    M -> M -> Prop :=
| RCUENil : forall formula,
    RawCodedUniversalEliminationChain M formula formula
| RCUECons : forall body replacement instance target,
    RawCodedFormulaSingleSubstitution M replacement body instance ->
    RawCodedUniversalEliminationChain M instance target ->
    RawCodedUniversalEliminationChain M
      (rawFormulaAllCode M body) target.

Arguments RCUENil {M} formula.
Arguments RCUECons {M} body replacement instance target _ _.
Arguments RawCodedUniversalEliminationChain M source target
  : clear implicits.

(** Metatheoretic traversal of a fixed template's leading universal tower.
    Failure is explicit when a caller asks to eliminate more binders than
    the source actually has.  All carrier-valued work remains in the
    translated operation traces proved below. *)
Fixpoint templateUniversalOpenMany
    (source : TemplateFormula) (replacements : list TemplateTerm)
    : option TemplateFormula :=
  match replacements with
  | [] => Some source
  | replacement :: tail =>
      match source with
      | tfAll body =>
          templateUniversalOpenMany
            (templateFormulaOpen replacement body) tail
      | _ => None
      end
  end.

(** Every successful fixed-template traversal produces the corresponding
    represented elimination chain under any honest compiler translation. *)
Theorem raw_templateUniversalOpenMany_elimination_chain : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    source replacements target,
  templateUniversalOpenMany source replacements = Some target ->
  RawCodedUniversalEliminationChain M
    (rawTemplateFormula translation source)
    (rawTemplateFormula translation target).
Proof.
  intros M translation source replacements.
  revert source.
  induction replacements as [|replacement tail ih];
    intros source target hopen.
  - cbn [templateUniversalOpenMany] in hopen.
    inversion hopen. constructor.
  - destruct source; try discriminate.
    cbn [templateUniversalOpenMany] in hopen.
    rewrite (rawTemplateFormula_all translation source).
    apply (RCUECons
      (rawTemplateFormula translation source)
      (rawTemplateTerm translation replacement)
      (rawTemplateFormula translation
        (templateFormulaOpen replacement source))
      (rawTemplateFormula translation target)).
    + exact (rawTemplateFormula_open translation source replacement).
    + exact (ih (templateFormulaOpen replacement source) target hopen).
Qed.

(** Compile every link in one unchanged context.  The returned root is
    existential because clients consume [RawCodedPALocalProofOf], not a
    particular syntactic association of the nested [allE] nodes. *)
Theorem raw_codedPALocalProofOf_universal_elimination_chain : forall
    (M : RawPAModel), RawPASatisfies M -> forall context source target,
  RawCodedUniversalEliminationChain M source target ->
  forall sourceRoot,
  RawCodedPALocalProofOf M context source sourceRoot ->
  exists targetRoot,
    RawCodedPALocalProofOf M context target targetRoot.
Proof.
  intros M hPA context source target hchain.
  induction hchain as
    [formula | body replacement instance target hsubstitution
      htail ihtail]; intros sourceRoot hsource.
  - exists sourceRoot. exact hsource.
  - pose proof (raw_codedPALocalProofOf_allE M hPA context
      body replacement instance sourceRoot hsource hsubstitution)
      as hinstance.
    exact (ihtail
      (rawProofAllERoot M context body replacement sourceRoot)
      hinstance).
Qed.

(** Compile a fixed PA theorem over an arbitrary witnessed base and then
    immediately specialize any finite number of its leading universal
    quantifiers.  The theorem is deliberately generic in the template
    translation: direct structural translations and ordinary quoted
    translations share the same implementation. *)
Theorem
    raw_codedTemplatePALocalProofOf_of_BProv_then_universal_chain_on_witnessed_tail
    : forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext phi target,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  Formula.BProv Formula.Ax_s [] phi ->
  RawCodedUniversalEliminationChain M
    (rawTemplateFormula translation (embedPAFormula phi)) target ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      target root.
Proof.
  intros M hPA translation hagreement
    baseWitnessList baseContext phi target hbase htheorem hchain.
  destruct (raw_codedTemplatePALocalProofOf_of_BProv_on_witnessed_tail
    M hPA translation hagreement baseWitnessList baseContext phi
    hbase htheorem) as
    (witnesses & sourceRoot & hextended & hsource).
  destruct (raw_codedPALocalProofOf_universal_elimination_chain
    M hPA
    (rawStandardPAAxiomWitnessPrefixContextCode M witnesses baseContext)
    (rawTemplateFormula translation (embedPAFormula phi)) target
    hchain sourceRoot hsource) as [root hroot].
  exists witnesses, root. split; assumption.
Qed.

(** User-facing fixed-template form: calculate the leading openings in
    [TemplateFormula], realize their represented traces automatically, and
    compile the fixed PA theorem plus all eliminations on one witnessed
    context. *)
Corollary
    raw_codedTemplatePALocalProofOf_of_BProv_open_many_on_witnessed_tail :
  forall (M : RawPAModel), RawPASatisfies M ->
  forall (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall baseWitnessList baseContext phi replacements targetTemplate,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  Formula.BProv Formula.Ax_s [] phi ->
  templateUniversalOpenMany
    (embedPAFormula phi) replacements = Some targetTemplate ->
  exists (witnesses : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses baseWitnessList)
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext) /\
    RawCodedPALocalProofOf M
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses baseContext)
      (rawTemplateFormula translation targetTemplate) root.
Proof.
  intros M hPA translation hagreement baseWitnessList baseContext
    phi replacements targetTemplate hbase htheorem hopen.
  apply
    (raw_codedTemplatePALocalProofOf_of_BProv_then_universal_chain_on_witnessed_tail
      M hPA translation hagreement baseWitnessList baseContext phi
      (rawTemplateFormula translation targetTemplate)
      hbase htheorem).
  exact (raw_templateUniversalOpenMany_elimination_chain
    M translation (embedPAFormula phi) replacements targetTemplate hopen).
Qed.

End PABoundedRawCodedPALocalProofUniversalEliminationChain.
