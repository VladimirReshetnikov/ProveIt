(**
  A closed PA source theorem for splitting a successor bound.

  The model-theoretic arithmetic library already proves

      i < S b  ->  i < b \/ i = b.

  Traversal extension needs the same statement as an actual model-coded PA
  proof, so this file packages it as a closed ordinary PA theorem.  The outer
  binders are [index] then [bound]; in the body, therefore, [index] is variable
  one and [bound] is variable zero.
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import RawModelCompleteness.

Module PABoundedRawCodedLtSuccCasesSource.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawModelCompleteness.

Definition codedLtSuccCasesFormula : formula :=
  pAll (pAll
    (pImp
      (Formula.ltTermAt (tVar 1) (tSucc (tVar 0)))
      (pOr
        (Formula.ltTermAt (tVar 1) (tVar 0))
        (pEq (tVar 1) (tVar 0))))).

Theorem codedLtSuccCasesFormula_sentence :
  Formula.Sentence codedLtSuccCasesFormula.
Proof.
  intros free hfree.
  unfold codedLtSuccCasesFormula, Formula.ltTermAt in hfree.
  cbn in hfree. lia.
Qed.

Theorem codedLtSuccCasesFormula_raw_valid : forall
    (M : RawPAModel), RawPASatisfies M -> forall e,
  raw_formula_sat M e codedLtSuccCasesFormula.
Proof.
  intros M hPA e.
  unfold codedLtSuccCasesFormula.
  cbn [raw_formula_sat raw_term_eval scons].
  intros index bound hbelow.
  exact (raw_lt_succ_cases M hPA index bound hbelow).
Qed.

Theorem PA_proves_codedLtSuccCasesFormula :
  Formula.BProv Formula.Ax_s [] codedLtSuccCasesFormula.
Proof.
  apply PA_BProv_of_raw_valid.
  - exact codedLtSuccCasesFormula_sentence.
  - exact codedLtSuccCasesFormula_raw_valid.
Qed.

End PABoundedRawCodedLtSuccCasesSource.
