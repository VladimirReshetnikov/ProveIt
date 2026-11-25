import IPRADerivations.Analysis.RationalCofactorBorderedRows
import IPRADerivations.Core.LinearCombination

/-!
# Exact transport from original rational cells to the cleared row

The SAME positive common denominator scales each original rational cell
into the actual integer-cleared cell used by the bordered determinant.
Its embedded scale is nonzero. Zero cancellation is proved for arbitrary
raw Gaussian operands through their canonical reads, and literally for
canonical operands or embedded original rational values.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofactorOriginalClearing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (app)
open RationalSupMetric (commonDenominator commonDenominator_one_le normalizedList coordinate)
open RationalSelectedMinors (fromInteger scale positive_scale_nonzero)
open RationalMatrixClearingBounds (cleared_representation)
open RationalCofactorBorderedRows (clearedCell)
open RationalGaussianEmbedding (embed embed_canonical embed_multiply)
open RationalPolynomialGaussianEmbedding (embed_congr)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalHorner (canonical qzero qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open GaussianTranslatedNonconstant (recode recode_canonical recode_eq)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem common_denominator_positive (P d : PTm n) : Γ ⊢[PRAAx] le one (commonDenominator P d) := commonDenominator_one_le P d
theorem scale_canonical (P d : PTm n) : Γ ⊢[PRAAx] canonical (scale P d) := embed_canonical _
theorem scale_nonzero (P d : PTm n) : Γ ⊢[PRAAx] neg (scale P d ≐ qzero) := positive_scale_nonzero P d

/-- Original rational multiplication, before the Gaussian embedding. Both
representations are derived from the actual clearing program. -/
theorem cleared_rational_scale (P d i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P)) (hj : Γ ⊢[PRAAx] lt j d) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply (GaussianRationalSyntheticBounds.natCode (commonDenominator P d)) (cell P i j) ≐
      fromInteger (cell (normalizedList P d) i j) := by
  let D := commonDenominator P d
  let s := GaussianRationalSyntheticBounds.natCode D
  let q := cell P i j
  let a := coordinate (entry (normalizedList P d) i) j
  have hD : Γ ⊢[PRAAx] le one D := commonDenominator_one_le P d
  have scaled := RationalRepresentations.represents_multiply (Γ := Γ) s q (ZT.ofNat D) a one D
    (GaussianRationalSyntheticBounds.natCode_represents D) (cleared_representation P d i j hi hj)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalNormalForm.normalize_well_formed a one (le_refl one)) scaled
    (RationalIntegerNormalization.normalize_preserves_value a one (le_refl one))
    (positive_product _ _ (le_refl one) hD) (le_refl one)
  ipra_lc

/-- Each actual cleared Gaussian cell equals the SAME embedded denominator
times the original embedded rational cell. Only original index bounds enter. -/
theorem cleared_cell_scale (P d i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P)) (hj : Γ ⊢[PRAAx] lt j d) : Γ ⊢[PRAAx]
    clearedCell P d i j ≐ qmul (scale P d) (embed (cell P i j)) :=
  (embed_congr (cleared_rational_scale P d i j hi hj).eqSymm).eqTrans (embed_multiply _ _)

/-- Raw Gaussian inputs cancel to their canonical field read. -/
theorem cancel_scaled_zero (P d z : PTm n) (h : Γ ⊢[PRAAx] qmul (scale P d) z ≐ qzero) : Γ ⊢[PRAAx] recode z ≐ qzero :=
  GaussianRationalFiniteRoots.product_zero_reflect _ _ (scale_canonical P d) (recode_canonical z) (scale_nonzero P d)
    ((GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqTrans h)
theorem scaled_zero_of_recode_zero (P d z : PTm n) (h : Γ ⊢[PRAAx] recode z ≐ qzero) : Γ ⊢[PRAAx]
    qmul (scale P d) z ≐ qzero :=
  (GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) h).eqTrans (qmul_zero_right _))
theorem scaled_zero_iff (P d z : PTm n) : Γ ⊢[PRAAx] Fm.iff (qmul (scale P d) z ≐ qzero) (recode z ≐ qzero) :=
  .andI (.impI (cancel_scaled_zero P d z Prf.hyp0)) (.impI (scaled_zero_of_recode_zero P d z Prf.hyp0))

theorem cancel_scaled_zero_canonical (P d z : PTm n) (hz : Γ ⊢[PRAAx] canonical z) (h : Γ ⊢[PRAAx] qmul (scale P d) z ≐ qzero) :
    Γ ⊢[PRAAx] z ≐ qzero := (recode_eq z hz).eqSymm.eqTrans (cancel_scaled_zero P d z h)
theorem cancel_embedded_zero (P d q : PTm n) (h : Γ ⊢[PRAAx] qmul (scale P d) (embed q) ≐ qzero) : Γ ⊢[PRAAx] embed q ≐ qzero :=
  cancel_scaled_zero_canonical P d (embed q) (embed_canonical q) h

theorem original_cell_zero_of_cleared (P d i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P)) (hj : Γ ⊢[PRAAx] lt j d)
    (h : Γ ⊢[PRAAx] clearedCell P d i j ≐ qzero) : Γ ⊢[PRAAx] embed (cell P i j) ≐ qzero :=
  cancel_embedded_zero P d (cell P i j) ((cleared_cell_scale P d i j hi hj).eqSymm.eqTrans h)
theorem cleared_cell_zero_iff (P d i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P)) (hj : Γ ⊢[PRAAx] lt j d) : Γ ⊢[PRAAx]
    Fm.iff (clearedCell P d i j ≐ qzero) (embed (cell P i j) ≐ qzero) :=
  .andI (.impI (original_cell_zero_of_cleared P d i j hi.wk hj.wk Prf.hyp0))
    (.impI ((cleared_cell_scale P d i j hi.wk hj.wk).eqTrans ((qmul_congr (.eqRefl _) Prf.hyp0).eqTrans (qmul_zero_right _))))

def output (P d i j : PTm n) : PTm n := pairT (clearedCell P d i j)
  (pairT (scale P d) (pairT (embed (cell P i j)) (commonDenominator P d)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (P d i j : PTm n) : PTm n := app outputF ![P,d,i,j]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (P d i j : PTm n) :
    Syn.subst σ (output P d i j) = output (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) (Syn.subst σ j) := by simp [output]
theorem program_at (P d i j : PTm n) : Γ ⊢[PRAAx] run P d i j ≐ output P d i j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,d,i,j]
theorem returned_cleared (P d i j : PTm n) : Γ ⊢[PRAAx] fstT (run P d i j) ≐ clearedCell P d i j :=
  (congrFst (program_at P d i j)).eqTrans (fst_pair _ _)
theorem returned_tail (P d i j : PTm n) : Γ ⊢[PRAAx] sndT (run P d i j) ≐ pairT (scale P d) (pairT (embed (cell P i j)) (commonDenominator P d)) :=
  (congrSnd (program_at P d i j)).eqTrans (snd_pair _ _)
theorem returned_scale (P d i j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run P d i j)) ≐ scale P d :=
  (congrFst (returned_tail P d i j)).eqTrans (fst_pair _ _)
theorem returned_source (P d i j : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run P d i j)) ≐ pairT (embed (cell P i j)) (commonDenominator P d) :=
  (congrSnd (returned_tail P d i j)).eqTrans (snd_pair _ _)
theorem returned_original (P d i j : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run P d i j))) ≐ embed (cell P i j) :=
  (congrFst (returned_source P d i j)).eqTrans (fst_pair _ _)
theorem returned_denominator (P d i j : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run P d i j))) ≐ commonDenominator P d :=
  (congrSnd (returned_source P d i j)).eqTrans (snd_pair _ _)
theorem returned_cell_scale (P d i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P)) (hj : Γ ⊢[PRAAx] lt j d) : Γ ⊢[PRAAx]
    fstT (run P d i j) ≐ qmul (scale P d) (embed (cell P i j)) :=
  (returned_cleared P d i j).eqTrans (cleared_cell_scale P d i j hi hj)

theorem actual_common_scale_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (commonDenominator (var 0) (var 1)) ⋏ neg (scale (var 0) (var 1) ≐ qzero)) :=
  closeUniv 2 (.andI (common_denominator_positive _ _) (scale_nonzero _ _))
theorem actual_original_cleared_cell_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (length (var 0)) ⟶ lt (var 3) (var 1) ⟶ clearedCell (var 0) (var 1) (var 2) (var 3) ≐
      qmul (scale (var 0) (var 1)) (embed (cell (var 0) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (cleared_cell_scale _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_common_scale_raw_cancel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qmul (scale (var 0) (var 1)) (var 2) ≐ qzero ⟶ recode (var 2) ≐ qzero) :=
  closeUniv 3 (.impI (cancel_scaled_zero _ _ _ Prf.hyp0))
theorem actual_common_scale_canonical_cancel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (canonical (var 2) ⟶ qmul (scale (var 0) (var 1)) (var 2) ≐ qzero ⟶ var 2 ≐ qzero) :=
  closeUniv 3 (.impI (.impI (cancel_scaled_zero_canonical _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_cleared_zero_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (length (var 0)) ⟶ lt (var 3) (var 1) ⟶
      Fm.iff (clearedCell (var 0) (var 1) (var 2) (var 3) ≐ qzero) (embed (cell (var 0) (var 2) (var 3)) ≐ qzero)) :=
  closeUniv 4 (.impI (.impI (cleared_cell_zero_iff _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_original_clearing_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_cleared_cell_scale_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (length (var 0)) ⟶ lt (var 3) (var 1) ⟶ fstT (run (var 0) (var 1) (var 2) (var 3)) ≐
      qmul (scale (var 0) (var 1)) (embed (cell (var 0) (var 2) (var 3)))) :=
  closeUniv 4 (.impI (.impI (returned_cell_scale _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalCofactorOriginalClearing
