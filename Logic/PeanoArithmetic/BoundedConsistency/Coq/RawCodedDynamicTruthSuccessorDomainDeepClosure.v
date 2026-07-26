(**
  Deep closure of the actual Sigma and Pi successor-domain witnesses.

  Each domain is obtained by substituting a possibly nonstandard numeral
  term into a fixed formula template.  Meta-level substitution cannot be
  used to inspect that numeral.  Instead its represented numeral certificate
  proves that every term shift and every term opening fixes it.  The concrete
  formula interchange laws then transport the fixed action of the template
  across the supplied single-substitution trace.

  The resulting cutoff 26 is the one seen by the domain conjunct underneath
  the eight existential row binders (the local row itself starts at 18).
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedAssignment RawCodedFormulaRankStep
  RawCodedFormulaOperations
  RawCodedTermEvaluationRealization
  RawCodedNumeralTermCode RawCodedNumeralTermShift
  RawCodedNumeralTermOpening RawCodedFormulaShiftTotality
  RawCodedFormulaShiftTreeRealization
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedStandardFormulaScopeDecision
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthGlobalSuccessorRootClosure
  RawCodedDynamicTruthGlobalSuccessorDeepClosure
  RawCodedFormulaShiftSubstitutionInterchangeInduction
  RawCodedFormulaSubstitutionAtomSubstitutionInterchangeInduction.

Module PABoundedRawCodedDynamicTruthSuccessorDomainDeepClosure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedNumeralTermShift.
Import PABoundedRawCodedNumeralTermOpening.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedStandardFormulaScopeDecision.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorRootClosure.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.
Import PABoundedRawCodedFormulaShiftSubstitutionInterchangeInduction.
Import
  PABoundedRawCodedFormulaSubstitutionAtomSubstitutionInterchangeInduction.

(** The two fixed templates have exactly twelve available external term
    variables before the numeral placeholder is removed. *)
Lemma dynamicTruthSigmaRowDomainTemplate_scoped_12 :
  StandardFormulaScoped 12 dynamicTruthSigmaRowDomainTemplate.
Proof.
  apply (proj1
    (standardFormulaScopedb_spec 12 dynamicTruthSigmaRowDomainTemplate)).
  reflexivity.
Qed.

Lemma dynamicTruthPiRowDomainTemplate_scoped_12 :
  StandardFormulaScoped 12 dynamicTruthPiRowDomainTemplate.
Proof.
  apply (proj1
    (standardFormulaScopedb_spec 12 dynamicTruthPiRowDomainTemplate)).
  reflexivity.
Qed.

(** Any cutoff above 26, once incremented to enter the source template, is
    certainly above the template's native scope 12. *)
Lemma raw_dynamicTruth_scope_twelve_below_successor_of_twenty_six : forall
    (M : RawPAModel), RawPASatisfies M -> forall cutoff,
  rawLe M (rawNumeralValue M 26) cutoff ->
  rawLe M (rawNumeralValue M 12) (raw_succ M cutoff).
Proof.
  intros M hPA cutoff hcutoff.
  eapply (raw_le_trans M hPA
    (rawNumeralValue M 12) (rawNumeralValue M 26)
    (raw_succ M cutoff)).
  - apply rawLe_numerals_of_le; [exact hPA | lia].
  - eapply (raw_le_trans M hPA
      (rawNumeralValue M 26) cutoff (raw_succ M cutoff)).
    + exact hcutoff.
    + apply raw_lt_to_le.
      exact (raw_assignment_lt_self_succ M hPA cutoff).
Qed.

(** An arbitrary honest replacement acts identically on a numeral term.
    Shift totality constructs its protected lift; the numeral traversal then
    serves unchanged as the source and target opening traversal. *)
Lemma raw_codedFormulaSubstitutionAtom_numeral_identity_of_syntax : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      replacement assignmentCode assignmentStep numeralBound numeral depth,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  RawNumeralTermCodeAt M numeralBound numeral ->
  RawCodedFormulaSubstitutionAtom M replacement depth numeral numeral.
Proof.
  intros M hPA replacement assignmentCode assignmentStep
    numeralBound numeral depth hreplacement hnumeral.
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    replacement assignmentCode assignmentStep hreplacement
    (raw_zero M) depth) as [liftedReplacement hshift].
  exists liftedReplacement. split.
  - exact hshift.
  - exact (raw_codedTermOpening_numeral_identity M hPA
      numeralBound numeral depth liftedReplacement hnumeral).
Qed.

(** Generic one-hole template theorem.  Scope twelve is all that the fixed
    Sigma/Pi source templates need; the result is stated at 26 because that
    is the exact depth consumed by successor-row assembly. *)
Theorem raw_codedSuccessorDomain_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      template numeralBound numeral domain,
  StandardFormulaScoped 12 template ->
  RawNumeralTermCodeAt M numeralBound numeral ->
  RawCodedFormulaSingleSubstitution M numeral
    (rawNumeralValue M (formulaCode template)) domain ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26) domain.
Proof.
  intros M hPA template numeralBound numeral domain
    htemplateScoped hnumeral hdomain.
  pose proof (raw_fixedFormulaNumeralCode_deep_closed_from_scope
    M hPA 12 template htemplateScoped) as htemplateDeep.
  unfold rawFixedFormulaNumeralCode in htemplateDeep.
  destruct htemplateDeep as
    [_ [htemplateShift htemplateSubstitution]].
  split.
  - exact (raw_dynamicTruthDomain_target_atomically_adequate
      M hPA numeralBound numeral (formulaCode template) domain
      hnumeral hdomain).
  - split.
    + intros cutoff amount hcutoff.
      exact (raw_codedFormulaShiftAtom_singleSubstitutionInterchange
        M hPA amount cutoff numeral numeral
        (rawNumeralValue M (formulaCode template))
        (rawNumeralValue M (formulaCode template)) domain domain
        (raw_codedTermShift_numeral_identity M hPA
          numeralBound numeral cutoff amount hnumeral)
        (htemplateShift (raw_succ M cutoff) amount
          (raw_dynamicTruth_scope_twelve_below_successor_of_twenty_six
            M hPA cutoff hcutoff))
        hdomain hdomain).
    + intros replacement assignmentCode assignmentStep depth
        hreplacement hdepth.
      exact
        (raw_codedFormulaSubstitutionAtom_singleSubstitutionInterchange
          M hPA replacement depth numeral numeral
          (rawNumeralValue M (formulaCode template))
          (rawNumeralValue M (formulaCode template)) domain domain
          (raw_codedFormulaSubstitutionAtom_numeral_identity_of_syntax
            M hPA replacement assignmentCode assignmentStep
            numeralBound numeral depth hreplacement hnumeral)
          (htemplateSubstitution replacement assignmentCode assignmentStep
            (raw_succ M depth) hreplacement
            (raw_dynamicTruth_scope_twelve_below_successor_of_twenty_six
              M hPA depth hdepth))
          hdomain hdomain).
Qed.

(** Exact Sigma witness interface used by the paired successor row. *)
Theorem raw_dynamicTruthSigmaSuccessorDomain_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lowerLevel numeral domain,
  RawNumeralTermCodeAt M (raw_succ M lowerLevel) numeral ->
  RawCodedFormulaSingleSubstitution M numeral
    (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode) domain ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26) domain.
Proof.
  intros M hPA lowerLevel numeral domain hnumeral hdomain.
  unfold dynamicTruthSigmaRowDomainTemplateCode in hdomain.
  exact (raw_codedSuccessorDomain_deep_closed M hPA
    dynamicTruthSigmaRowDomainTemplate (raw_succ M lowerLevel)
    numeral domain dynamicTruthSigmaRowDomainTemplate_scoped_12
    hnumeral hdomain).
Qed.

(** Exact Pi witness interface used by the paired successor row. *)
Theorem raw_dynamicTruthPiSuccessorDomain_deep_closed : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      lowerLevel numeral domain,
  RawNumeralTermCodeAt M (raw_succ M lowerLevel) numeral ->
  RawCodedFormulaSingleSubstitution M numeral
    (rawNumeralValue M (formulaCode dynamicTruthPiRowDomainTemplate))
    domain ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26) domain.
Proof.
  intros M hPA lowerLevel numeral domain hnumeral hdomain.
  exact (raw_codedSuccessorDomain_deep_closed M hPA
    dynamicTruthPiRowDomainTemplate (raw_succ M lowerLevel)
    numeral domain dynamicTruthPiRowDomainTemplate_scoped_12
    hnumeral hdomain).
Qed.

End PABoundedRawCodedDynamicTruthSuccessorDomainDeepClosure.
