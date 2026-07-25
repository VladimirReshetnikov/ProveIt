(**
  Atomic adequacy of the paired rank-zero dynamic-truth seed.

  The paired base graph has law-free numeral witnesses, but the strengthened
  orbit needs witnesses carrying internal formula-syntax certificates.  In a
  PA model we choose the equal structural quotations of the two fixed
  ternary predicates and apply standard quotation adequacy to each one.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedProofAtomicAdequacyStandard
  RawCodedCarrierIndexedPairedAdequateCodeOrbitGraph
  RawCodedDynamicTruthFixedSyntaxFragments
  RawCodedDynamicTruthPairedBaseFormulaCodeGraph.

Module PABoundedRawCodedDynamicTruthPairedBaseAdequacy.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofAtomicAdequacyStandard.
Import PABoundedRawCodedCarrierIndexedPairedAdequateCodeOrbitGraph.
Import PABoundedRawCodedDynamicTruthFixedSyntaxFragments.
Import PABoundedRawCodedDynamicTruthPairedBaseFormulaCodeGraph.

(** This is the exact base interface consumed by adequacy-preserving paired
    PA induction. *)
Theorem dynamicTruthPairedBaseFormulaCodeGraph_adequate_total : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierIndexedPairedAdequateCodeOrbitBaseTotal M
    dynamicTruthPairedBaseFormulaCodeGraph.
Proof.
  intros M hPA tail.
  exists (rawQuotedFormulaCode M dynamicTruthBaseTernaryFormula).
  exists (rawQuotedFormulaCode M dynamicTruthPiBaseTernaryFormula).
  split.
  - exact (dynamicTruthPairedBaseFormulaCodeGraph_quoted M hPA tail).
  - split.
    + apply raw_quotedFormula_atomically_adequate. exact hPA.
    + apply raw_quotedFormula_atomically_adequate. exact hPA.
Qed.

End PABoundedRawCodedDynamicTruthPairedBaseAdequacy.
