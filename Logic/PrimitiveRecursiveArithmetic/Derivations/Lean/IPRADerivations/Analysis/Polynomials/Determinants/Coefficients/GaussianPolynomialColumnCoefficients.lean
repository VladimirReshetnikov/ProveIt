import IPRADerivations.Analysis.Polynomials.Determinants.Multilinearity.GaussianPolynomialColumnAlternation
import IPRADerivations.Analysis.RationalArithmetic.Grids.GaussianRationalFiniteGridIdentity

/-!
# Actual determinant coefficient negation under an adjacent column swap

The same determinant programs are added as actual coefficient lists. Their
Horner evaluations cancel by the proved numerical column action. A genuine
finite grid, with distinctness and its computed root bound derived from
actual codes, forces every coefficient of this actual sum to vanish.
Canonical output coefficients then yield literal coefficient negation and
bounded equality with the actual scaled negative polynomial. All dimensions,
widths and queries are numerical. No evaluator, grid-root, coefficient or
outer-list identity is supplied as an original input contract.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialColumnCoefficients

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnegative qnegative_canonical qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr canonical_coefficient_at)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (added added_length added_lookup added_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling (scaled scaled_length scaled_lookup)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (tableShape)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def original (M m L : PTm n) : PTm n := GaussianPolynomialDeterminant.determinant M m L
def swapped (M m L j : PTm n) : PTm n :=
  GaussianPolynomialDeterminant.determinant (GaussianPolynomialColumnAlternation.CS M m j) m L
def cancellation (M m L j : PTm n) : PTm n := added (swapped M m L j) (original M m L) (succ (m*L))
def negativePolynomial (M m L : PTm n) : PTm n :=
  scaled (original M m L) GaussianRationalMatrixFiniteSums.minusOne
ipra_subst original
ipra_subst swapped
ipra_subst cancellation
ipra_subst negativePolynomial

theorem original_length (M m L : PTm n) : Γ ⊢[PRAAx] length (original M m L) ≐ succ (m*L) :=
  GaussianPolynomialDeterminant.determinant_length _ _ _
theorem swapped_length (M m L j : PTm n) : Γ ⊢[PRAAx] length (swapped M m L j) ≐ succ (m*L) :=
  GaussianPolynomialDeterminant.determinant_length _ _ _
theorem cancellation_length (M m L j : PTm n) : Γ ⊢[PRAAx] length (cancellation M m L j) ≐ succ (m*L) := added_length _ _ _
theorem negative_length (M m L : PTm n) : Γ ⊢[PRAAx] length (negativePolynomial M m L) ≐ succ (m*L) :=
  (scaled_length _ _).eqTrans (original_length _ _ _)
theorem original_canonical (M m L : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalSyntheticDivision.canonicalCoefficients (original M m L) :=
  GaussianPolynomialDeterminant.determinant_canonical _ _ _
theorem swapped_canonical (M m L j : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalSyntheticDivision.canonicalCoefficients (swapped M m L j) :=
  GaussianPolynomialDeterminant.determinant_canonical _ _ _
theorem cancellation_canonical (M m L j : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalSyntheticDivision.canonicalCoefficients (cancellation M m L j) :=
  GaussianRationalMonicReduction.added_canonical _ _ _

/-- This grid-root contract is derived from the SAME actual determinant
programs and only the original table shape and active adjacent-column guard. -/
theorem cancellation_evaluation (M m L j z : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx] evaluate (cancellation M m L j) z ≐ qzero :=
  (added_evaluation _ _ _ z (swapped_length _ _ _ _) (original_length _ _ _)).eqTrans
    (GaussianPolynomialColumnAlternation.column_evaluation_cancel _ _ _ _ _ hM hj)
theorem cancellation_grid_roots (M m L j : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    GaussianRationalFiniteRoots.roots (cancellation M m L j) (GaussianRationalFiniteGridIdentity.grid (m*L)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift M) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using hM.shift
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_cancellation,PTm.subst_mul,GaussianRationalFiniteGridIdentity.subst_grid] using
    cancellation_evaluation (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j)
      (entry (GaussianRationalFiniteGridIdentity.grid (Syn.shift m*Syn.shift L)) (var 0)) hs.wk js.wk

theorem cancellation_all_zero (M m L j : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    GaussianRationalPolynomialDegree.allZero (cancellation M m L j) (m*L) :=
  GaussianRationalFiniteGridIdentity.finite_grid_zero _ _ (cancellation_length _ _ _ _) (cancellation_grid_roots _ _ _ _ hM hj)

theorem bounded_coefficient_range (C d s : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ d)
    (hs : Γ ⊢[PRAAx] le s d) : Γ ⊢[PRAAx] lt s (length C) :=
  lt_congr (.eqRefl _) hC.eqSymm ((succ_monus_succ _ _).eqTrans hs)
theorem cancellation_coefficient_zero (M m L j s : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (cancellation M m L j) s ≐ qzero :=
  (GaussianTranslatedNonconstant.recode_eq _
    (canonical_coefficient_at _ _ (cancellation_canonical _ _ _ _)
      (bounded_coefficient_range _ _ _ (cancellation_length _ _ _ _) hs))).eqSymm.eqTrans
    (GaussianRationalFiniteGridIdentity.coefficient_zero _ _ _ (cancellation_length _ _ _ _)
      (cancellation_grid_roots _ _ _ _ hM hj) hs)

/-- Raw b is permitted; only a must already be canonical for literal recovery. -/
theorem qadd_zero_left_negative (a b : PTm n) (ha : Γ ⊢[PRAAx] canonical a)
    (h : Γ ⊢[PRAAx] qadd a b ≐ qzero) : Γ ⊢[PRAAx] a ≐ qnegative b :=
  (GaussianReciprocalHorner.qsub_add_cancel a b ha).eqSymm.eqTrans
    ((GaussianRationalSyntheticDivision.qsub_congr h (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (qnegative_canonical _)))

theorem column_coefficient_neg (M m L j s : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (swapped M m L j) s ≐ qnegative (entry (original M m L) s) :=
  qadd_zero_left_negative _ _
    (canonical_coefficient_at _ _ (swapped_canonical _ _ _ _) (bounded_coefficient_range _ _ _ (swapped_length _ _ _ _) hs))
    ((added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs)).eqSymm.eqTrans
      (cancellation_coefficient_zero _ _ _ _ _ hM hj hs))

theorem negative_coefficient (M m L s : PTm n) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (negativePolynomial M m L) s ≐ qnegative (entry (original M m L) s) :=
  (scaled_lookup _ _ _ (bounded_coefficient_range _ _ _ (original_length _ _ _) hs)).eqTrans
    (GaussianRationalMatrixFiniteSums.negative_as_minusOne _).eqSymm
theorem column_coefficient_scaled (M m L j s : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (swapped M m L j) s ≐ entry (negativePolynomial M m L) s :=
  (column_coefficient_neg _ _ _ _ _ hM hj hs).eqTrans (negative_coefficient _ _ _ _ hs).eqSymm

/-- The existing table/determinant payload is retained, alongside the two
actual polynomial buffers used by the coefficient proof. -/
def output (M m L j : PTm n) : PTm n := pairT (GaussianPolynomialColumnAlternation.run M m L j)
  (pairT (cancellation M m L j) (negativePolynomial M m L))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (M m L j : PTm n) : PTm n := app outputF ![M,m,L,j]
ipra_subst output
ipra_subst run
theorem program_at (M m L j : PTm n) : Γ ⊢[PRAAx] run M m L j ≐ output M m L j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3)) ![M,m,L,j]
theorem returned_column_program (M m L j : PTm n) : Γ ⊢[PRAAx]
    fstT (run M m L j) ≐ GaussianPolynomialColumnAlternation.run M m L j :=
  (program_at _ _ _ _).fstE
theorem returned_cancellation (M m L j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run M m L j)) ≐ cancellation M m L j :=
  (program_at _ _ _ _).sndE.fstE
theorem returned_negative (M m L j : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run M m L j)) ≐ negativePolynomial M m L :=
  (program_at _ _ _ _).sndE.sndE
theorem returned_original_polynomial (M m L j : PTm n) : Γ ⊢[PRAAx]
    fstT (fstT (sndT (fstT (run M m L j)))) ≐ original M m L :=
  (congrFst (congrFst (congrSnd (returned_column_program _ _ _ _)))).eqTrans
    (GaussianPolynomialColumnAlternation.returned_original_polynomial _ _ _ _)
theorem returned_swapped_polynomial (M m L j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (fstT (run M m L j)))) ≐ swapped M m L j :=
  (congrFst (congrSnd (congrSnd (returned_column_program _ _ _ _)))).eqTrans
    (GaussianPolynomialColumnAlternation.returned_swapped_polynomial _ _ _ _)
theorem returned_coefficient_neg (M m L j s : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) (hs : Γ ⊢[PRAAx] le s (m*L)) : Γ ⊢[PRAAx]
    entry (fstT (sndT (sndT (fstT (run M m L j))))) s ≐
      qnegative (entry (fstT (fstT (sndT (fstT (run M m L j))))) s) :=
  (entry_congr (returned_swapped_polynomial _ _ _ _) (.eqRefl _)).eqTrans
    ((column_coefficient_neg _ _ _ _ _ hM hj hs).eqTrans
      (GaussianInverseBinomialRows.negative_congr (entry_congr (returned_original_polynomial _ _ _ _) (.eqRefl _))).eqSymm)

/-! Ordinary closed derivations bind every original table, numerical size,
column and coefficient query. No extensional outer-list equality is asserted. -/
theorem actual_cancellation_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (cancellation (var 0) (var 1) (var 2) (var 3)) ≐ succ (var 1*var 2)) :=
  closeUniv 4 (cancellation_length _ _ _ _)
theorem actual_cancellation_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ lt (succ (var 3)) (var 1) ⟶
      evaluate (cancellation (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (cancellation_evaluation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cancellation_grid_roots_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (tableShape (var 0) (var 1) (var 2) ⟶ lt (succ (var 3)) (var 1) ⟶
      GaussianRationalFiniteRoots.roots (cancellation (var 0) (var 1) (var 2) (var 3))
        (GaussianRationalFiniteGridIdentity.grid (var 1*var 2))) :=
  closeUniv 4 (.impI (.impI (cancellation_grid_roots _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_cancellation_coefficient_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ lt (succ (var 3)) (var 1) ⟶ le (var 4) (var 1*var 2) ⟶
      entry (cancellation (var 0) (var 1) (var 2) (var 3)) (var 4) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (.impI (cancellation_coefficient_zero _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_column_coefficient_neg_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ lt (succ (var 3)) (var 1) ⟶ le (var 4) (var 1*var 2) ⟶
      entry (swapped (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        qnegative (entry (original (var 0) (var 1) (var 2)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (column_coefficient_neg _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_column_coefficient_scaled_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ lt (succ (var 3)) (var 1) ⟶ le (var 4) (var 1*var 2) ⟶
      entry (swapped (var 0) (var 1) (var 2) (var 3)) (var 4) ≐
        entry (negativePolynomial (var 0) (var 1) (var 2)) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (column_coefficient_scaled _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_coefficient_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)
theorem returned_coefficient_neg_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ lt (succ (var 3)) (var 1) ⟶ le (var 4) (var 1*var 2) ⟶
      entry (fstT (sndT (sndT (fstT (run (var 0) (var 1) (var 2) (var 3)))))) (var 4) ≐
        qnegative (entry (fstT (fstT (sndT (fstT (run (var 0) (var 1) (var 2) (var 3)))))) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (returned_coefficient_neg _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialColumnCoefficients
