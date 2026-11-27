import IPRADerivations.Analysis.Polynomials.Elimination.Vandermonde.GaussianVandermondeCompletionElimination
import IPRADerivations.Analysis.Polynomials.Elimination.Vandermonde.GaussianVandermondeNewtonMatrix
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianFiberDeterminantNonzero

/-!
# Literal product for the original completed Vandermonde determinant

An actual extended Newton change is multiplied after the actual left
eliminator of the original completion W. All cells of both products are
derived from the original Gaussian finite sums. The resulting table is
lower triangular, and the SAME determinant's two multiplicativity laws
and real diagonal fold give the literal forward pair-difference product.
All dimensions are numerical, including the empty list and dimension.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompletedVandermondeProduct

open_ipra
open GaussianRationalHorner (qzero qmul canonical canonical_congr evaluate)
open GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical qmul_congr)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open GaussianRationalReciprocal (power)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalFiberVandermonde (delta W weight table table_lookup)
open GaussianRationalMatrixFiniteSums (matrixProduct scalarDot scalarBody scalarData product_lookup scalar_body_at)
open GaussianScalarDeterminant (scalarDet scalar_det_canonical)
open GaussianScalarTriangularDeterminant (belowZeros aboveZeros diagonalOnes diagonalProduct)
open GaussianVandermondeNewtonPolynomials (coefficient polynomial differenceProduct pairProduct)
open GaussianVandermondeCompletionElimination (eliminator eliminated delta_congr delta_symm cut_unequal)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! Genuine raw-safe local coordinate row/column transport for the actual dot. -/
def columnBody : PTm 2 := cell (fstT (var 1)) (var 0) (sndT (var 1))
def rowBody : PTm 2 := cell (fstT (var 1)) (sndT (var 1)) (var 0)
theorem column_body_at (A j k : PTm n) : Γ ⊢[PRAAx] inst2 columnBody k (pairT A j) ≐ cell A k j := by
  simp only [columnBody,inst2,GaussianPolynomialDeterminantTerms.subst_cell,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact entry_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)
theorem row_body_at (A r k : PTm n) : Γ ⊢[PRAAx] inst2 rowBody k (pairT A r) ≐ cell A r k := by
  simp only [rowBody,inst2,GaussianPolynomialDeterminantTerms.subst_cell,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact entry_congr (entry_congr (fst_pair _ _) (snd_pair _ _)) (.eqRefl _)
def deltaRow (A m r : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶
  cell (Syn.shift A) (Syn.shift r) (var 0) ≐ delta (Syn.shift r) (var 0))
def deltaColumn (A m j : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶
  cell (Syn.shift A) (var 0) (Syn.shift j) ≐ delta (var 0) (Syn.shift j))
ipra_subst deltaRow [Syn.subst_shift, Syn.shift_subst]
ipra_subst deltaColumn [Syn.subst_shift, Syn.shift_subst]

theorem left_delta_dot (A B m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (h : Γ ⊢[PRAAx] deltaRow A m r) : Γ ⊢[PRAAx]
    scalarDot A B m r j ≐ recode (cell B r j) := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody
      (GaussianRationalMatrixFiniteSums.deltaBody columnBody) m (scalarData A B r j) (pairT r (pairT B j)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have hs : Γ.map Fm.shift ⊢[PRAAx] deltaRow (Syn.shift A) (Syn.shift m) (Syn.shift r) := by
      simpa [Fm.shift,Syn.shift] using h.shift
    have row : Δ ⊢[PRAAx] cell (Syn.shift A) (Syn.shift r) (var 0) ≐ delta (Syn.shift r) (var 0) := .impE h.allOpen.wk Prf.hyp0
    have actual := (scalar_body_at (Γ := Δ) (Syn.shift A) (Syn.shift B) (Syn.shift r) (Syn.shift j) (var 0)).eqTrans
      ((qmul_congr row (.eqRefl _)).eqTrans
        ((GaussianRationalMatrixFiniteSums.delta_body_at columnBody (Syn.shift r) (var 0) (pairT (Syn.shift B) (Syn.shift j))).eqTrans
          (qmul_congr (.eqRefl _) (column_body_at _ _ _))).eqSymm)
    simpa only [Δ,Syn.shift,GaussianRationalMatrixFiniteSums.subst_scalarData,subst_pairT] using actual
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_delta columnBody m r (pairT B j) hr).eqTrans (recode_congr (column_body_at _ _ _)))

theorem right_delta_dot (A B m r j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) (h : Γ ⊢[PRAAx] deltaColumn B m j) : Γ ⊢[PRAAx]
    scalarDot A B m r j ≐ recode (cell A r j) := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody
      (GaussianRationalMatrixFiniteSums.deltaBody rowBody) m (scalarData A B r j) (pairT j (pairT A r)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have hs : Γ.map Fm.shift ⊢[PRAAx] deltaColumn (Syn.shift B) (Syn.shift m) (Syn.shift j) := by
      simpa [Fm.shift,Syn.shift] using h.shift
    have column : Δ ⊢[PRAAx] cell (Syn.shift B) (var 0) (Syn.shift j) ≐ delta (var 0) (Syn.shift j) := .impE h.allOpen.wk Prf.hyp0
    have actual := (scalar_body_at (Γ := Δ) (Syn.shift A) (Syn.shift B) (Syn.shift r) (Syn.shift j) (var 0)).eqTrans
      ((qmul_congr (.eqRefl _) column).eqTrans
        ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
          ((qmul_congr (delta_symm _ _) (.eqRefl _)).eqTrans
            ((GaussianRationalMatrixFiniteSums.delta_body_at rowBody (Syn.shift j) (var 0) (pairT (Syn.shift A) (Syn.shift r))).eqTrans
              (qmul_congr (.eqRefl _) (row_body_at _ _ _))).eqSymm)))
    simpa only [Δ,Syn.shift,GaussianRationalMatrixFiniteSums.subst_scalarData,subst_pairT] using actual
  exact (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_delta rowBody m j (pairT A r) hj).eqTrans (recode_congr (row_body_at _ _ _)))

/-- The coefficient change on the original cut, identity after it. -/
def extendedWeight (R r j : PTm n) : PTm n := sel (Signum.sg (monus (length R) j)) (coefficient R j r) (delta r j)
def extendedBody : PTm 3 := extendedWeight (var 2) (var 0) (var 1)
def extended (R m : PTm n) : PTm n := table extendedBody m m R
def completed (R m : PTm n) : PTm n := matrixProduct (eliminated R m) (extended R m) m
ipra_subst extendedWeight [sel, Signum.sg]
ipra_subst extended
ipra_subst completed
theorem extended_head (R r j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    extendedWeight R r j ≐ coefficient R j r := sel_one (AnalyticNumberTheory.Totatives.sg_lt hj)
theorem extended_tail (R r j : PTm n) (hj : Γ ⊢[PRAAx] le (length R) j) : Γ ⊢[PRAAx]
    extendedWeight R r j ≐ delta r j := sel_zero (AnalyticNumberTheory.Totatives.sg_le hj)
theorem extended_lower (R r j : PTm n) (hr : Γ ⊢[PRAAx] le (length R) r) : Γ ⊢[PRAAx]
    extendedWeight R r j ≐ delta r j := by
  refine .orE (lt_or_le j (length R)) ?_ (extended_tail _ _ _ Prf.hyp0)
  exact (extended_head _ _ _ Prf.hyp0).eqTrans
    ((GaussianVandermondeNewtonPolynomials.coefficient_above _ _ _ (lt_of_lt_of_le Prf.hyp0 hr.wk)).eqTrans
      ((delta_symm r j).eqTrans (GaussianRationalLagrangeCardinals.delta_unequal _ _ (cut_unequal _ _ _ Prf.hyp0 hr.wk))).eqSymm)
theorem extended_canonical (R r j : PTm n) : Γ ⊢[PRAAx] canonical (extendedWeight R r j) := by
  refine .orE (lt_or_le j (length R)) ?_ ?_
  · exact canonical_congr (extended_head _ _ _ Prf.hyp0) (GaussianVandermondeNewtonPolynomials.coefficient_canonical _ _ _)
  · exact canonical_congr (extended_tail _ _ _ Prf.hyp0) (GaussianRationalFiberVandermonde.delta_canonical _ _)
theorem extended_lookup (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (extended R m) r j ≐ extendedWeight R r j := by
  simpa [extended,extendedBody] using table_lookup extendedBody m m R r j hr hj

theorem extended_upper_at (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m)
    (hjr : Γ ⊢[PRAAx] lt j r) : Γ ⊢[PRAAx] recode (cell (extended R m) r j) ≐ qzero := by
  have zero : Γ ⊢[PRAAx] extendedWeight R r j ≐ qzero := by
    refine .orE (lt_or_le j (length R)) ?_ ?_
    · exact (extended_head _ _ _ Prf.hyp0).eqTrans (GaussianVandermondeNewtonPolynomials.coefficient_above _ _ _ hjr.wk)
    · have ne : le (length R) j :: Γ ⊢[PRAAx] neg (r ≐ j) := .impI (lt_irrefl j _ (lt_congr (.eqRefl _) Prf.hyp0 hjr.wk.wk))
      exact (extended_tail _ _ _ Prf.hyp0).eqTrans (GaussianRationalLagrangeCardinals.delta_unequal _ _ ne)
  exact (recode_congr ((extended_lookup _ _ _ _ hr hj).eqTrans zero)).eqTrans (recode_eq qzero qzero_canonical)
theorem extended_one_at (R m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    recode (cell (extended R m) r r) ≐ qone := by
  have one : Γ ⊢[PRAAx] extendedWeight R r r ≐ qone := by
    refine .orE (lt_or_le r (length R)) ?_ ?_
    · exact (extended_head _ _ _ Prf.hyp0).eqTrans (GaussianVandermondeNewtonPolynomials.coefficient_diagonal _ _)
    · exact (extended_tail _ _ _ Prf.hyp0).eqTrans (GaussianRationalLagrangeCardinals.delta_equal _ _ (.eqRefl _))
  exact (recode_congr ((extended_lookup _ _ _ _ hr hr).eqTrans one)).eqTrans (recode_eq qone qone_canonical)
theorem extended_upper (R m : PTm n) : Γ ⊢[PRAAx] belowZeros (extended R m) m := by
  refine .allI (.impI (.allI (.impI (.impI ?_))))
  let Δ := lt (var 0) (var 1) :: lt (var 0) (Syn.shift (Syn.shift m)) ::
    (lt (var 0) (Syn.shift m)).shift :: (Γ.map Fm.shift).map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa [Δ,Fm.shift,Syn.shift] using (Prf.hyp0.wk.wk : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift)
  have actual := extended_upper_at (Γ := Δ) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift m)) (var 1) (var 0) hr Prf.hyp1 Prf.hyp0
  simpa [Δ,belowZeros,GaussianScalarTriangularDeterminant.belowRow,Fm.shift,Syn.shift] using actual
theorem extended_diagonal_ones (R m : PTm n) : Γ ⊢[PRAAx] diagonalOnes (extended R m) m := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_extended] using extended_one_at (Syn.shift R) (Syn.shift m) (var 0) Prf.hyp0
theorem extended_det (R m : PTm n) : Γ ⊢[PRAAx] scalarDet (extended R m) m ≐ qone :=
  GaussianScalarTriangularDeterminant.unit_triangular_det _ _ (.orI₁ (extended_upper _ _)) (extended_diagonal_ones _ _)

theorem eliminated_delta_row (R m r : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hr : Γ ⊢[PRAAx] le (length R) r) : Γ ⊢[PRAAx]
    deltaRow (eliminated R m) m r := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have rms : Δ ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hrm.shift.wk : Δ ⊢[PRAAx] (lt r m).shift)
  have rs : Δ ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift r) := by simpa [Δ,Fm.shift,Syn.shift] using (hr.shift.wk : Δ ⊢[PRAAx] (le (length R) r).shift)
  simpa only [Δ,Syn.shift,GaussianVandermondeCompletionElimination.subst_eliminated] using
    GaussianVandermondeCompletionElimination.eliminated_lower (Γ := Δ) (Syn.shift R) (Syn.shift m) (Syn.shift r) (var 0) rms Prf.hyp0 rs

theorem extended_delta_column (R m j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) (hjt : Γ ⊢[PRAAx] le (length R) j) : Γ ⊢[PRAAx]
    deltaColumn (extended R m) m j := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have jms : Δ ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hj.shift.wk : Δ ⊢[PRAAx] (lt j m).shift)
  have js : Δ ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift j) := by simpa [Δ,Fm.shift,Syn.shift] using (hjt.shift.wk : Δ ⊢[PRAAx] (le (length R) j).shift)
  simpa only [Δ,Syn.shift,subst_extended] using
    (extended_lookup (Γ := Δ) (Syn.shift R) (Syn.shift m) (var 0) (Syn.shift j) Prf.hyp0 jms).eqTrans (extended_tail _ _ _ js)

theorem completed_lower_rows (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] le (length R) r) : Γ ⊢[PRAAx] cell (completed R m) r j ≐ delta r j :=
  (product_lookup _ _ _ _ _ hrm hjm).eqTrans
    ((left_delta_dot _ _ _ _ _ hrm (eliminated_delta_row _ _ _ hrm hr)).eqTrans
      ((recode_congr ((extended_lookup _ _ _ _ hrm hjm).eqTrans (extended_lower _ _ _ hr))).eqTrans
        (recode_eq _ (GaussianRationalFiberVandermonde.delta_canonical _ _))))
theorem completed_upper_right (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] le (length R) j) : Γ ⊢[PRAAx]
    cell (completed R m) r j ≐ qzero :=
  (product_lookup _ _ _ _ _ hrm hjm).eqTrans
    ((right_delta_dot _ _ _ _ _ hjm (extended_delta_column _ _ _ hjm hj)).eqTrans
      ((recode_congr (GaussianVandermondeCompletionElimination.eliminated_upper_right _ _ _ _ hrm hjm hr hj)).eqTrans
        (recode_eq qzero qzero_canonical)))

theorem completed_upper_left (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    cell (completed R m) r j ≐ evaluate (polynomial R j) (entry R r) := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual scalarBody GaussianVandermondeNewtonPolynomials.powerBody m
      (scalarData (eliminated R m) (extended R m) r j) (GaussianVandermondeNewtonPolynomials.powerData R j (entry R r)) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have rms : Δ ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hrm.shift.wk : Δ ⊢[PRAAx] (lt r m).shift)
    have jms : Δ ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by simpa [Δ,Fm.shift,Syn.shift] using (hjm.shift.wk : Δ ⊢[PRAAx] (lt j m).shift)
    have rs : Δ ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by simpa [Δ,Fm.shift,Syn.shift] using (hr.shift.wk : Δ ⊢[PRAAx] (lt r (length R)).shift)
    have js : Δ ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift R)) := by simpa [Δ,Fm.shift,Syn.shift] using (hj.shift.wk : Δ ⊢[PRAAx] (lt j (length R)).shift)
    have actual : Δ ⊢[PRAAx] qmul (cell (eliminated (Syn.shift R) (Syn.shift m)) (Syn.shift r) (var 0))
        (cell (extended (Syn.shift R) (Syn.shift m)) (var 0) (Syn.shift j)) ≐
          GaussianVandermondeNewtonPolynomials.term (Syn.shift R) (Syn.shift j) (entry (Syn.shift R) (Syn.shift r)) (var 0) := by
      refine .orE (lt_or_le (var 0) (length (Syn.shift R))) ?_ ?_
      · exact qmul_congr (GaussianVandermondeCompletionElimination.eliminated_upper_left _ _ _ _ rms.wk Prf.hyp1 rs.wk Prf.hyp0)
          ((extended_lookup _ _ _ _ Prf.hyp1 jms.wk).eqTrans (extended_head _ _ _ js.wk))
      · have zeroRight : le (length (Syn.shift R)) (var 0) :: Δ ⊢[PRAAx]
            GaussianVandermondeNewtonPolynomials.term (Syn.shift R) (Syn.shift j) (entry (Syn.shift R) (Syn.shift r)) (var 0) ≐ qzero :=
          (qmul_congr (.eqRefl _) (GaussianVandermondeNewtonPolynomials.coefficient_above _ _ _
            (lt_of_lt_of_le js.wk Prf.hyp0))).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)
        exact ((qmul_congr (GaussianVandermondeCompletionElimination.eliminated_upper_right _ _ _ _ rms.wk Prf.hyp1 rs.wk Prf.hyp0) (.eqRefl _)).eqTrans
          (GaussianRationalSyntheticDivision.qmul_zero_left _)).eqTrans zeroRight.eqSymm
    have full := (scalar_body_at (Γ := Δ) (eliminated (Syn.shift R) (Syn.shift m)) (extended (Syn.shift R) (Syn.shift m))
      (Syn.shift r) (Syn.shift j) (var 0)).eqTrans (actual.eqTrans (GaussianVandermondeNewtonPolynomials.power_body_at _ _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,GaussianVandermondeCompletionElimination.subst_eliminated,subst_extended,
      GaussianRationalMatrixFiniteSums.subst_scalarData,GaussianVandermondeNewtonPolynomials.subst_powerData,
      Foundations.MasterCertificate.subst_entry] using full
  exact (product_lookup _ _ _ _ _ hrm hjm).eqTrans ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
    (GaussianVandermondeNewtonPolynomials.power_sum_evaluation _ _ _ _ hjm))

theorem completed_above_at (R m r j : PTm n) (hrm : Γ ⊢[PRAAx] lt r m) (hjm : Γ ⊢[PRAAx] lt j m)
    (hrj : Γ ⊢[PRAAx] lt r j) : Γ ⊢[PRAAx] cell (completed R m) r j ≐ qzero := by
  have ne : Γ ⊢[PRAAx] neg (r ≐ j) := .impI (lt_irrefl j _ (lt_congr Prf.hyp0 (.eqRefl _) hrj.wk))
  refine .orE (lt_or_le r (length R)) ?_ ?_
  · refine .orE (lt_or_le j (length R)) ?_ ?_
    · exact (completed_upper_left _ _ _ _ hrm.wk.wk hjm.wk.wk Prf.hyp1 Prf.hyp0).eqTrans
        (GaussianVandermondeNewtonPolynomials.prior_root_zero _ _ _ hrj.wk.wk)
    · exact completed_upper_right _ _ _ _ hrm.wk.wk hjm.wk.wk Prf.hyp1 Prf.hyp0
  · exact (completed_lower_rows _ _ _ _ hrm.wk hjm.wk Prf.hyp0).eqTrans (GaussianRationalLagrangeCardinals.delta_unequal _ _ ne.wk)

theorem completed_lower (R m : PTm n) : Γ ⊢[PRAAx] aboveZeros (completed R m) m := by
  refine .allI (.impI (.allI (.impI (.impI ?_))))
  let Δ := lt (var 1) (var 0) :: lt (var 0) (Syn.shift (Syn.shift m)) ::
    (lt (var 0) (Syn.shift m)).shift :: (Γ.map Fm.shift).map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa [Δ,Fm.shift,Syn.shift] using (Prf.hyp0.wk.wk : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift)
  have actual := (recode_congr (completed_above_at (Γ := Δ) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift m))
    (var 1) (var 0) hr Prf.hyp1 Prf.hyp0)).eqTrans (recode_eq qzero qzero_canonical)
  simpa [Δ,aboveZeros,GaussianScalarTriangularDeterminant.aboveRow,Fm.shift,Syn.shift] using actual

theorem completed_head_diagonal (R m j : PTm n) (hjm : Γ ⊢[PRAAx] lt j m) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    cell (completed R m) j j ≐ differenceProduct R (entry R j) j :=
  (completed_upper_left _ _ _ _ hjm hjm hj hj).eqTrans (GaussianVandermondeNewtonPolynomials.diagonal_evaluation _ _)
theorem completed_tail_diagonal (R m j : PTm n) (hjm : Γ ⊢[PRAAx] lt j m) (hj : Γ ⊢[PRAAx] le (length R) j) : Γ ⊢[PRAAx]
    cell (completed R m) j j ≐ qone :=
  (completed_lower_rows _ _ _ _ hjm hjm hj).eqTrans (GaussianRationalLagrangeCardinals.delta_equal _ _ (.eqRefl _))

theorem head_diagonal_product (R m : PTm n) (htm : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    GaussianRationalFiniteProduct.qprod GaussianScalarTriangularDeterminant.diagonalBody (length R) (completed R m) ≐ pairProduct R (length R) := by
  refine GaussianRationalFiniteProduct.product_congr_bounded GaussianScalarTriangularDeterminant.diagonalBody
    GaussianVandermondeNewtonPolynomials.pairBody (length R) (completed R m) R (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift
  have ht : Δ ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift m) := by
    simpa [Δ,Fm.shift,Syn.shift] using (htm.shift.wk : Δ ⊢[PRAAx] (le (length R) m).shift)
  have hi : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift R)) := by
    simpa [Δ,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (length R)))
  have actual := completed_head_diagonal (Γ := Δ) (Syn.shift R) (Syn.shift m) (var 0) (lt_of_lt_of_le hi ht) hi
  simpa only [Δ,Syn.shift,GaussianScalarTriangularDeterminant.diagonal_body_at,
    GaussianVandermondeNewtonPolynomials.pair_body_at,subst_completed] using actual

theorem tail_diagonal_product (R m : PTm n) (htm : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    GaussianRationalFiniteProduct.qprod (offB GaussianScalarTriangularDeterminant.diagonalBody)
      (monus m (length R)) (pairT (length R) (completed R m)) ≐ qone := by
  refine GaussianRationalProductAlgebra.product_one_of_terms _ _ _ (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift (monus m (length R))) :: Γ.map Fm.shift
  have ht : Δ ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift m) := by
    simpa [Δ,Fm.shift,Syn.shift] using (htm.shift.wk : Δ ⊢[PRAAx] (le (length R) m).shift)
  have hi : Δ ⊢[PRAAx] lt (var 0) (monus (Syn.shift m) (length (Syn.shift R))) := by
    simpa [Δ,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (monus m (length R))))
  have addBound : Δ ⊢[PRAAx] lt (length (Syn.shift R)+var 0)
      (length (Syn.shift R)+monus (Syn.shift m) (length (Syn.shift R))) := by ipra_le sl hi
  have bound := lt_congr (.eqRefl _) (eq_add_of_le ht).eqSymm addBound
  have offset := GaussianRationalFiniteProduct.offset_at (Γ := Δ) GaussianScalarTriangularDeterminant.diagonalBody
    (length (Syn.shift R)) (var 0) (completed (Syn.shift R) (Syn.shift m))
  rw [GaussianScalarTriangularDeterminant.diagonal_body_at] at offset
  have actual := offset.eqTrans (completed_tail_diagonal _ _ _ bound (le_add_right _ _))
  simpa only [Δ,Syn.shift,subst_pairT,Foundations.SequenceComposition.subst_length,subst_completed,
    inst2,GaussianRationalSyntheticDivision.subst_qone] using actual

theorem completed_diagonal_product (R m : PTm n) (htm : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    diagonalProduct (completed R m) m ≐ pairProduct R (length R) :=
  (GaussianRationalFiniteProduct.product_index_congr GaussianScalarTriangularDeterminant.diagonalBody (eq_add_of_le htm) (.eqRefl _)).eqTrans
    ((GaussianRationalFiniteProduct.product_split _ (length R) (monus m (length R)) (completed R m)).eqTrans
      ((qmul_congr (head_diagonal_product R m htm) (tail_diagonal_product R m htm)).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (GaussianVandermondeNewtonPolynomials.pair_canonical _ _))))

theorem eliminated_det (R m : PTm n) : Γ ⊢[PRAAx] scalarDet (eliminated R m) m ≐ scalarDet (W R m) m :=
  (GaussianScalarDeterminantMultiplication.scalar_det_multiply _ _ _).eqTrans
    ((qmul_congr (GaussianVandermondeCompletionElimination.eliminator_det _ _) (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (scalar_det_canonical _ _))))
theorem completed_det (R m : PTm n) : Γ ⊢[PRAAx] scalarDet (completed R m) m ≐ scalarDet (W R m) m :=
  (GaussianScalarDeterminantMultiplication.scalar_det_multiply _ _ _).eqTrans
    ((qmul_congr (.eqRefl _) (extended_det _ _)).eqTrans
      ((GaussianReciprocalHorner.qmul_one_right _ (scalar_det_canonical _ _)).eqTrans (eliminated_det R m)))

theorem determinant_product (R m : PTm n) (htm : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    scalarDet (W R m) m ≐ pairProduct R (length R) :=
  (completed_det R m).eqSymm.eqTrans
    ((GaussianScalarTriangularDeterminant.lower_triangular_det _ _ (completed_lower R m)).eqTrans (completed_diagonal_product R m htm))

/-- The SAME existing determinant of the actual original constant-polynomial table WP. -/
def constantPolynomial (R m : PTm n) : PTm n := GaussianFiberDeterminantNonzero.polynomial R m
ipra_subst constantPolynomial
theorem constant_polynomial_product (R m z : PTm n) (htm : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    evaluate (constantPolynomial R m) z ≐ pairProduct R (length R) :=
  (GaussianFiberDeterminantNonzero.polynomial_evaluation _ _ _).eqTrans (determinant_product R m htm)
theorem constant_coefficient_product (R m : PTm n) (htm : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    entry (constantPolynomial R m) zero ≐ pairProduct R (length R) :=
  (GaussianFiberDeterminantNonzero.polynomial_coefficient _ _).eqTrans (determinant_product R m htm)
theorem pair_product_nonzero (R : PTm n) (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R) : Γ ⊢[PRAAx]
    neg (pairProduct R (length R) ≐ qzero) :=
  .impI (.impE (GaussianFiberDeterminantNonzero.determinant_nonzero (Γ := (pairProduct R (length R) ≐ qzero) :: Γ)
      R (length R) hDistinct.wk (le_refl _))
    ((determinant_product R (length R) (le_refl _)).wk.eqTrans Prf.hyp0))

def output (R m : PTm n) : PTm n := pairT (W R m) (pairT (extended R m) (pairT (completed R m)
  (pairT (scalarDet (W R m) m) (pairT (pairProduct R (length R)) (constantPolynomial R m)))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (R m : PTm n) : PTm n := app outputF ![R,m]
def fields (p : PTm n) : Fin 6 → PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),
  fstT (sndT (sndT (sndT p))),fstT (sndT (sndT (sndT (sndT p)))),sndT (sndT (sndT (sndT (sndT p))))]
ipra_subst output
ipra_subst run
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 6) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i :=
  subst_pairVectorField σ 5 p i
theorem program_at (R m : PTm n) : Γ ⊢[PRAAx] run R m ≐ output R m := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![R,m]
theorem returned_fields (R m : PTm n) (i : Fin 6) : Γ ⊢[PRAAx] fields (run R m) i ≐
    ![W R m,extended R m,completed R m,scalarDet (W R m) m,pairProduct R (length R),constantPolynomial R m] i :=
  pairVectorField_eq 5 _ (program_at R m) i
theorem returned_product (R m : PTm n) (htm : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    fields (run R m) 3 ≐ fields (run R m) 4 :=
  (returned_fields R m 3).eqTrans ((determinant_product R m htm).eqTrans (returned_fields R m 4).eqSymm)
theorem returned_polynomial_value (R m z : PTm n) (htm : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    evaluate (fields (run R m) 5) z ≐ fields (run R m) 4 :=
  (GaussianRationalMonicReduction.evaluate_congr (returned_fields R m 5) (.eqRefl _)).eqTrans
    ((constant_polynomial_product R m z htm).eqTrans (returned_fields R m 4).eqSymm)

theorem actual_extended_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶ cell (extended (var 0) (var 1)) (var 2) (var 3) ≐
      extendedWeight (var 0) (var 2) (var 3)) := closeUniv 4 (.impI (.impI (extended_lookup _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_extended_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarDet (extended (var 0) (var 1)) (var 1) ≐ qone) := closeUniv 2 (extended_det _ _)
theorem actual_completed_upper_left_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶ lt (var 3) (length (var 0)) ⟶
      cell (completed (var 0) (var 1)) (var 2) (var 3) ≐ evaluate (polynomial (var 0) (var 3)) (entry (var 0) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (completed_upper_left _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_completed_upper_right_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶ le (length (var 0)) (var 3) ⟶
      cell (completed (var 0) (var 1)) (var 2) (var 3) ≐ qzero) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (completed_upper_right _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_completed_lower_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶ le (length (var 0)) (var 2) ⟶
      cell (completed (var 0) (var 1)) (var 2) (var 3) ≐ delta (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (completed_lower_rows _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_completed_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (aboveZeros (completed (var 0) (var 1)) (var 1)) := closeUniv 2 (completed_lower _ _)
theorem actual_completed_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarDet (completed (var 0) (var 1)) (var 1) ≐ scalarDet (W (var 0) (var 1)) (var 1)) := closeUniv 2 (completed_det _ _)
theorem actual_completed_vandermonde_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (length (var 0)) (var 1) ⟶ scalarDet (W (var 0) (var 1)) (var 1) ≐ pairProduct (var 0) (length (var 0))) :=
  closeUniv 2 (.impI (determinant_product _ _ Prf.hyp0))
theorem actual_original_polynomial_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (length (var 0)) (var 1) ⟶ evaluate (constantPolynomial (var 0) (var 1)) (var 2) ≐ pairProduct (var 0) (length (var 0))) :=
  closeUniv 3 (.impI (constant_polynomial_product _ _ _ Prf.hyp0))
theorem actual_original_coefficient_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (length (var 0)) (var 1) ⟶ entry (constantPolynomial (var 0) (var 1)) zero ≐ pairProduct (var 0) (length (var 0))) :=
  closeUniv 2 (.impI (constant_coefficient_product _ _ Prf.hyp0))
theorem actual_pair_product_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ neg (pairProduct (var 0) (length (var 0)) ≐ qzero)) :=
  closeUniv 1 (.impI (pair_product_nonzero _ Prf.hyp0))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (length (var 0)) (var 1) ⟶ fields (run (var 0) (var 1)) 3 ≐ fields (run (var 0) (var 1)) 4) :=
  closeUniv 2 (.impI (returned_product _ _ Prf.hyp0))
theorem actual_returned_polynomial_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (length (var 0)) (var 1) ⟶ evaluate (fields (run (var 0) (var 1)) 5) (var 2) ≐ fields (run (var 0) (var 1)) 4) :=
  closeUniv 3 (.impI (returned_polynomial_value _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompletedVandermondeProduct
