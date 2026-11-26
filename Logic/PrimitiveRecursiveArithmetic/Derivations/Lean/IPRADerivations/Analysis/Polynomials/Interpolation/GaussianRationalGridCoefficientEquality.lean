import IPRADerivations.Analysis.RationalArithmetic.Grids.GaussianRationalFiniteGridIdentity
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalValueEquality

/-!
# Two actual polynomial buffers agreeing on the numerical grid

The actual sum of the first buffer and the actual minus-one-scaled second
buffer vanishes on the constructed grid. Its computed finite-root bound
forces every original coefficient difference to vanish. Arbitrary raw
coefficient values consequently have equal canonical recodes; canonical
original coefficients yield literal code equality. Every width, original
buffer and grid/coefficient index is numerical, including width one.
No all-points identity or outer list-code extensionality is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalGridCoefficientEquality

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qadd_congr qsub_congr canonicalCoefficients canonical_coefficient_at)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers
  (added added_length added_lookup added_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling
  (scaled scaled_length scaled_lookup evaluation_linearity)
open LeanProofs.IPRA.Analysis.GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteGridIdentity (grid gridPoint grid_lookup grid_length)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_eq)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Original observations only at the N+1 actual constructed grid points. -/
def gridEqual (C D N : PTm n) : Fm PTm n := .all (le (var 0) (Syn.shift N) ⟶
  evaluate (Syn.shift C) (gridPoint (var 0)) ≐ evaluate (Syn.shift D) (gridPoint (var 0)))
def negativePolynomial (D : PTm n) : PTm n := scaled D minusOne
def difference (C D N : PTm n) : PTm n := added C (negativePolynomial D) (succ N)
def coefficientsEqual (C D N : PTm n) : Fm PTm n := .all (le (var 0) (Syn.shift N) ⟶
  entry (Syn.shift C) (var 0) ≐ entry (Syn.shift D) (var 0))
ipra_subst gridEqual [Syn.subst_shift, Syn.shift_subst]
ipra_subst negativePolynomial
ipra_subst difference
ipra_subst coefficientsEqual [Syn.subst_shift, Syn.shift_subst]

theorem grid_equal_at (C D N i : PTm n) (h : Γ ⊢[PRAAx] gridEqual C D N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] evaluate C (gridPoint i) ≐ evaluate D (gridPoint i) := by
  have rule : Γ ⊢[PRAAx] le i N ⟶ evaluate C (gridPoint i) ≐ evaluate D (gridPoint i) := by
    simpa [gridEqual] using h.allE i
  exact .impE rule hi

theorem bounded_coefficient_range (C N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] lt i (length C) :=
  lt_congr (.eqRefl _) hC.eqSymm ((succ_monus_succ _ _).eqTrans hi)
theorem negative_length (D : PTm n) : Γ ⊢[PRAAx] length (negativePolynomial D) ≐ length D := scaled_length _ _
theorem negative_coefficient (D i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length D)) : Γ ⊢[PRAAx]
    entry (negativePolynomial D) i ≐ GaussianRationalMetric.qnegative (entry D i) :=
  (scaled_lookup _ _ _ hi).eqTrans (negative_as_minusOne _).eqSymm
theorem negative_evaluation (D z : PTm n) : Γ ⊢[PRAAx]
    evaluate (negativePolynomial D) z ≐ GaussianRationalMetric.qnegative (evaluate D z) :=
  (evaluation_linearity _ _ _).eqTrans (negative_as_minusOne _).eqSymm
theorem difference_length (C D N : PTm n) : Γ ⊢[PRAAx] length (difference C D N) ≐ succ N := added_length _ _ _
theorem difference_canonical (C D N : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (difference C D N) :=
  GaussianRationalMonicReduction.added_canonical _ _ _
theorem difference_coefficient (C D N i : PTm n) (hD : Γ ⊢[PRAAx] length D ≐ succ N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (difference C D N) i ≐ qsub (entry C i) (entry D i) :=
  (added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hi)).eqTrans
    (qadd_congr (.eqRefl _) (negative_coefficient _ _ (bounded_coefficient_range _ _ _ hD hi)))
theorem difference_evaluation (C D N z : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] length D ≐ succ N) : Γ ⊢[PRAAx]
    evaluate (difference C D N) z ≐ qsub (evaluate C z) (evaluate D z) :=
  (added_evaluation _ _ _ _ hC ((negative_length D).eqTrans hD)).eqTrans
    (qadd_congr (.eqRefl _) (negative_evaluation _ _))

theorem difference_grid_value (C D N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] length D ≐ succ N) (h : Γ ⊢[PRAAx] gridEqual C D N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] evaluate (difference C D N) (gridPoint i) ≐ qzero :=
  (difference_evaluation _ _ _ _ hC hD).eqTrans
    ((qsub_congr (grid_equal_at _ _ _ _ h hi) (.eqRefl _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _))

theorem difference_grid_roots (C D N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] length D ≐ succ N) (h : Γ ⊢[PRAAx] gridEqual C D N) : Γ ⊢[PRAAx]
    GaussianRationalFiniteRoots.roots (difference C D N) (grid N) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift D) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hD.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] gridEqual (Syn.shift C) (Syn.shift D) (Syn.shift N) := by
    simpa only [Fm.shift,subst_gridEqual,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (grid N))) :: Γ.map Fm.shift
  have range : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)) :=
    lt_congr (.eqRefl _) (grid_length _) (by
      simpa only [Δ,Syn.shift,GaussianRationalFiniteGridIdentity.subst_grid] using
        (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift (grid N)))))
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := (succ_monus_succ _ _).eqSymm.eqTrans range
  have e := (GaussianRationalMonicReduction.evaluate_congr (.eqRefl _)
      (grid_lookup (Syn.shift N) (var 0) range)).eqTrans
    (difference_grid_value (Syn.shift C) (Syn.shift D) (Syn.shift N) (var 0) cs.wk ds.wk hs.wk hi)
  simpa only [Δ,Syn.shift,subst_difference,GaussianRationalFiniteGridIdentity.subst_grid] using e

theorem difference_coefficient_zero (C D N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] length D ≐ succ N) (h : Γ ⊢[PRAAx] gridEqual C D N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] qsub (entry C i) (entry D i) ≐ qzero := by
  have actual : Γ ⊢[PRAAx] entry (difference C D N) i ≐ qzero :=
    (recode_eq _ (canonical_coefficient_at _ _ (difference_canonical _ _ _)
      (bounded_coefficient_range _ _ _ (difference_length _ _ _) hi))).eqSymm.eqTrans
        (GaussianRationalFiniteGridIdentity.coefficient_zero _ _ _ (difference_length _ _ _)
          (difference_grid_roots _ _ _ hC hD h) hi)
  exact (difference_coefficient _ _ _ _ hD hi).eqSymm.eqTrans actual

/-- Raw inputs yield the exact equality of their independently canonical recodes. -/
theorem coefficient_recode_equal (C D N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] length D ≐ succ N) (h : Γ ⊢[PRAAx] gridEqual C D N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] recode (entry C i) ≐ recode (entry D i) :=
  (GaussianRationalValueEquality.recode_eq_iff_difference_zero _ _).iffMpr
    (difference_coefficient_zero _ _ _ _ hC hD h hi)

theorem coefficient_equal (C D N i : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] length D ≐ succ N) (hCanC : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hCanD : Γ ⊢[PRAAx] canonicalCoefficients D) (h : Γ ⊢[PRAAx] gridEqual C D N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] entry C i ≐ entry D i :=
  (recode_eq _ (canonical_coefficient_at _ _ hCanC (bounded_coefficient_range _ _ _ hC hi))).eqSymm.eqTrans
    ((coefficient_recode_equal _ _ _ _ hC hD h hi).eqTrans
      (recode_eq _ (canonical_coefficient_at _ _ hCanD (bounded_coefficient_range _ _ _ hD hi))))

theorem coefficients_equal (C D N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hD : Γ ⊢[PRAAx] length D ≐ succ N) (hCanC : Γ ⊢[PRAAx] canonicalCoefficients C)
    (hCanD : Γ ⊢[PRAAx] canonicalCoefficients D) (h : Γ ⊢[PRAAx] gridEqual C D N) : Γ ⊢[PRAAx]
    coefficientsEqual C D N := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift D) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hD.shift
  have ccs : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift C) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hCanC.shift
  have dcs : Γ.map Fm.shift ⊢[PRAAx] canonicalCoefficients (Syn.shift D) := by
    simpa only [Fm.shift,GaussianRationalSyntheticDivision.subst_canonicalCoefficients,Syn.shift] using hCanD.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] gridEqual (Syn.shift C) (Syn.shift D) (Syn.shift N) := by
    simpa only [Fm.shift,subst_gridEqual,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift] using coefficient_equal (Syn.shift C) (Syn.shift D) (Syn.shift N) (var 0)
    cs.wk ds.wk ccs.wk dcs.wk hs.wk Prf.hyp0

/-- Original shape, original coefficient canonicality and actual finite observations. -/
def input (C D N : PTm n) : Fm PTm n := (length C ≐ succ N) ⋏
  ((length D ≐ succ N) ⋏ (canonicalCoefficients C ⋏ (canonicalCoefficients D ⋏ gridEqual C D N)))
ipra_subst input
theorem coefficient_from_input (C D N i : PTm n) (h : Γ ⊢[PRAAx] input C D N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] entry C i ≐ entry D i :=
  coefficient_equal _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ h)))
    (.andE₁ (.andE₂ (.andE₂ (.andE₂ h)))) (.andE₂ (.andE₂ (.andE₂ (.andE₂ h)))) hi
theorem coefficients_from_input (C D N : PTm n) (h : Γ ⊢[PRAAx] input C D N) : Γ ⊢[PRAAx]
    coefficientsEqual C D N :=
  coefficients_equal _ _ _ (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ h)))
    (.andE₁ (.andE₂ (.andE₂ (.andE₂ h)))) (.andE₂ (.andE₂ (.andE₂ (.andE₂ h))))

/-- Actual difference/grid buffers and both selected ORIGINAL coefficient codes. -/
def output (C D N i : PTm n) : PTm n := pairT (difference C D N)
  (pairT (grid N) (pairT (entry C i) (entry D i)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (C D N i : PTm n) : PTm n := app outputF ![C,D,N,i]
ipra_subst output
ipra_subst run
theorem program_at (C D N i : PTm n) : Γ ⊢[PRAAx] run C D N i ≐ output C D N i := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,D,N,i]
theorem returned_difference (C D N i : PTm n) : Γ ⊢[PRAAx]
    fstT (run C D N i) ≐ difference C D N := (program_at _ _ _ _).fstE
theorem returned_grid (C D N i : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run C D N i)) ≐ grid N :=
  (program_at _ _ _ _).sndE.fstE
theorem returned_left (C D N i : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run C D N i))) ≐ entry C i :=
  (program_at _ _ _ _).sndE.sndE.fstE
theorem returned_right (C D N i : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run C D N i))) ≐ entry D i :=
  (program_at _ _ _ _).sndE.sndE.sndE
theorem returned_difference_length (C D N i : PTm n) : Γ ⊢[PRAAx] length (fstT (run C D N i)) ≐ succ N :=
  (congrFst (returned_difference _ _ _ _)).eqTrans (difference_length _ _ _)
theorem returned_grid_length (C D N i : PTm n) : Γ ⊢[PRAAx] length (fstT (sndT (run C D N i))) ≐ succ N :=
  (congrFst (returned_grid _ _ _ _)).eqTrans (grid_length _)
theorem returned_equal (C D N i : PTm n) (h : Γ ⊢[PRAAx] input C D N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run C D N i))) ≐ sndT (sndT (sndT (run C D N i))) :=
  (returned_left _ _ _ _).eqTrans ((coefficient_from_input _ _ _ _ h hi).eqTrans (returned_right _ _ _ _).eqSymm)

theorem actual_buffer_difference_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 2) ⟶
      evaluate (difference (var 0) (var 1) (var 2)) (var 3) ≐
        qsub (evaluate (var 0) (var 3)) (evaluate (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (difference_evaluation _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_difference_grid_roots_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 2) ⟶ gridEqual (var 0) (var 1) (var 2) ⟶
      GaussianRationalFiniteRoots.roots (difference (var 0) (var 1) (var 2)) (grid (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (difference_grid_roots _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_grid_raw_coefficient_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 2) ⟶ length (var 1) ≐ succ (var 2) ⟶ gridEqual (var 0) (var 1) (var 2) ⟶
      le (var 3) (var 2) ⟶ recode (entry (var 0) (var 3)) ≐ recode (entry (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (coefficient_recode_equal _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_grid_coefficient_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) ⟶ le (var 3) (var 2) ⟶ entry (var 0) (var 3) ≐ entry (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (coefficient_from_input _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_grid_buffer_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input (var 0) (var 1) (var 2) ⟶ coefficientsEqual (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (coefficients_from_input _ _ _ Prf.hyp0))
theorem actual_grid_comparison_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) ⋏
      (length (fstT (run (var 0) (var 1) (var 2) (var 3))) ≐ succ (var 2)) ⋏
      (length (fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ succ (var 2))) :=
  closeUniv 4 (.andI (program_at _ _ _ _) (.andI (returned_difference_length _ _ _ _) (returned_grid_length _ _ _ _)))
theorem actual_returned_grid_coefficient_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) ⟶ le (var 3) (var 2) ⟶
      fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 4 (.impI (.impI (returned_equal _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalGridCoefficientEquality
