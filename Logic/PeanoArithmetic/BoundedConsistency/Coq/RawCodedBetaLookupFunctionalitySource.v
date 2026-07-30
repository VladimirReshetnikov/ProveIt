(**
  A closed PA theorem expressing functionality of one beta-table lookup.

  The semantic beta API already proves that a fixed code and step have at
  most one output at a fixed index.  Successor-row compilation needs that
  fact as an object-level PA proof, because its two lookups are represented
  assumptions and the resulting output equality must itself be consumed by
  represented equality elimination.

  The outer binders are [out1], [out2], [code], [step], and [index].  Thus in
  the innermost body their de Bruijn indices are respectively 4, 3, 2, 1,
  and 0.  The conclusion uses the orientation [out2 = out1], matching PA's
  existing beta-functionality derivation.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import RawModelCompleteness.

Module PABoundedRawCodedBetaLookupFunctionalitySource.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.

Definition codedBetaLookupFunctionalityFormula : formula :=
  pAll (pAll (pAll (pAll (pAll
    (pImp
      (Formula.betaTermTermAt
        (tVar 4) (tVar 2) (tVar 1) (tVar 0))
      (pImp
        (Formula.betaTermTermAt
          (tVar 3) (tVar 2) (tVar 1) (tVar 0))
        (pEq (tVar 3) (tVar 4)))))))).

Theorem codedBetaLookupFunctionalityFormula_sentence :
  Formula.Sentence codedBetaLookupFunctionalityFormula.
Proof.
  intros free hfree.
  unfold codedBetaLookupFunctionalityFormula,
    Formula.betaTermTermAt, Formula.remTermTermAt,
    Formula.ltTermAt, Formula.betaModTermTerm in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedBetaLookupFunctionalityFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedBetaLookupFunctionalityFormula.
Proof.
  intros M hPA e.
  unfold codedBetaLookupFunctionalityFormula.
  cbn [raw_formula_sat].
  intros out1 out2 code step index hfirst hsecond.
  apply (proj1 (raw_sat_betaTermTermAt_iff M
    (tVar 4) (tVar 2) (tVar 1) (tVar 0)
    (scons M index
      (scons M step
        (scons M code (scons M out2 (scons M out1 e))))))) in hfirst.
  apply (proj1 (raw_sat_betaTermTermAt_iff M
    (tVar 3) (tVar 2) (tVar 1) (tVar 0)
    (scons M index
      (scons M step
        (scons M code (scons M out2 (scons M out1 e))))))) in hsecond.
  cbn [raw_term_eval scons] in hfirst, hsecond |- *.
  symmetry.
  exact (rawBetaEntry_functional M hPA
    out1 out2 code step index hfirst hsecond).
Qed.

Theorem PA_proves_codedBetaLookupFunctionalityFormula :
  Formula.BProv Formula.Ax_s [] codedBetaLookupFunctionalityFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedBetaLookupFunctionalityFormula_sentence.
  - exact codedBetaLookupFunctionalityFormula_raw_valid.
Qed.

End PABoundedRawCodedBetaLookupFunctionalitySource.
