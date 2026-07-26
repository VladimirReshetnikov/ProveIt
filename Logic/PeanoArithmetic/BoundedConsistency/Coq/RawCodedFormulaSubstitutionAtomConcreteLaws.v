(** Concrete lower laws consumed by deep ternary opening interchange. *)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations
  RawCodedTernaryPredicateDeepClosureOpeningInterchange
  RawCodedFormulaSubstitutionAtomSourceSyntax
  RawCodedFormulaSubstitutionAtomProtective
  RawCodedFormulaSubstitutionAtomSubstitutionInterchangeInduction.

Module PABoundedRawCodedFormulaSubstitutionAtomConcreteLaws.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningInterchange.
Import PABoundedRawCodedFormulaSubstitutionAtomSourceSyntax.
Import PABoundedRawCodedFormulaSubstitutionAtomProtective.
Import PABoundedRawCodedFormulaSubstitutionAtomSubstitutionInterchangeInduction.

(** Both algebra laws are in fact unconditional.  The syntax premise in the
    bridge record remains important at the public boundary: it prevents
    downstream clients from silently generalizing unrelated atom relations
    to malformed carrier values. *)
Theorem raw_codedFormulaSubstitutionAtom_concreteLawsOnSyntax : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaSubstitutionAtomConcreteLawsOnSyntax M.
Proof.
  intros M hPA. constructor.
  - intros replacement _.
    exact (raw_codedFormulaSubstitutionAtom_protectiveShiftStable
      M hPA replacement).
  - intros replacement _.
    exact (raw_codedFormulaSubstitutionAtom_singleSubstitutionInterchange
      M hPA replacement).
Qed.

(** The companion source-syntax theorem is re-exported under a record-adjacent
    name for short imports in the completion module. *)
Corollary raw_codedFormulaSubstitutionAtom_sourceSyntaxLaw : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedFormulaSubstitutionAtomSourceSyntax M.
Proof.
  exact raw_codedFormulaSubstitutionAtom_source_syntax.
Qed.

End PABoundedRawCodedFormulaSubstitutionAtomConcreteLaws.
