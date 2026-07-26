(**
  Unconditional opening commutation for a deeply closed ternary predicate.

  The guarded bridge is the logically important boundary: deep closure fixes
  substitution only for honestly represented replacement terms.  The
  concrete substitution atom nevertheless justifies the legacy relation,
  because every incoming atom contains a represented shift whose source is
  precisely that replacement.  Thus malformed carrier values cannot satisfy
  the antecedent, while all honest replacements receive the full represented
  substitution/substitution algebra.

  This final module contains no new induction.  It combines the source-syntax
  projection and concrete lower-law package with the deep-closure bridge and
  exports the exact selector contract consumed by the direct structural
  template translator.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTernaryPredicateDeepClosure
  RawCodedTernaryPredicateDeepClosureOpeningInterchange
  RawCodedFormulaSubstitutionAtomConcreteLaws.

Module PABoundedRawCodedTernaryPredicateDeepClosureOpeningCommuting.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningInterchange.
Import PABoundedRawCodedFormulaSubstitutionAtomConcreteLaws.

(** The old relation is now justified for every carrier-valued replacement:
    if its three atom premises exist, the first one recovers honest syntax;
    otherwise the implication is vacuous. *)
Theorem raw_codedTernaryApplicationOpeningInterchange_of_deepClosed_concrete :
  forall (M : RawPAModel), RawPASatisfies M -> forall predicate,
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawCodedTernaryApplicationOpeningInterchange M predicate.
Proof.
  intros M hPA predicate hdeep.
  exact (raw_codedTernaryApplicationOpeningInterchange_of_deepClosed
    M hPA predicate
    (raw_codedFormulaSubstitutionAtom_concreteLawsOnSyntax M hPA)
    (raw_codedFormulaSubstitutionAtom_sourceSyntaxLaw M hPA)
    hdeep).
Qed.

(** Exact honest-domain selector law required by
    [RawCodedDynamicTruthTemplateDirectInputs]. *)
Theorem
    rawTernaryApplicationSelector_opening_commuting_on_syntax_of_deepClosed_concrete :
  forall (M : RawPAModel), RawPASatisfies M -> forall predicate
    (selector : RawCodedTernaryApplicationSelector M predicate),
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawCodedTernaryApplicationOpeningCommutingOnSyntax
    M predicate selector.
Proof.
  intros M hPA predicate selector hdeep.
  exact
    (rawTernaryApplicationSelector_opening_commuting_on_syntax_of_deepClosed
      M hPA predicate selector
      (raw_codedFormulaSubstitutionAtom_concreteLawsOnSyntax M hPA)
      (raw_codedFormulaSubstitutionAtom_sourceSyntaxLaw M hPA)
      hdeep).
Qed.

End PABoundedRawCodedTernaryPredicateDeepClosureOpeningCommuting.
