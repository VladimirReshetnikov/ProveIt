import IPRADerivations.Analysis.Polynomials.CompanionMatrices.GaussianPolynomialMultiplicationMatrix
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminant

/-!
# Actual runtime monic multiplication-matrix norm polynomial

The original numerical coefficient rows produce the polynomial-valued
multiplication matrix, whose proved shape is fed to the actual determinant.
All dimensions, degree bounds, data and queries remain numerical. The full
polynomial, matrix and companion columns are returned by one actual PR5.
No matrix, determinant or evaluator law is an incoming source premise.

This concrete Q(i)[X] constructor proves the actual coefficient/evaluation
Leibniz formulas and curve-action binding. It does not yet prove norm
nonvanishing, sharp degree, matrix-kernel-to-norm-zero, fiber multiplicity,
a general coded-field interface or the annihilator theorem.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialMonicNorm

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (evaluate_congr canonical_coefficients_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialMonicCompanion (rowShape subst_rowShape values monicValues)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def width (m a c : PTm n) : PTm n := GaussianPolynomialMultiplicationMatrix.width m a c
def degreeBound (m a c : PTm n) : PTm n := m*width m a c
def matrix (F G m a c : PTm n) : PTm n := GaussianPolynomialMultiplicationMatrix.matrix F G m a c
def columns (F G m a c : PTm n) : PTm n := GaussianPolynomialMultiplicationMatrix.columns F G m a c
def norm (F G m a c : PTm n) : PTm n := GaussianPolynomialDeterminant.determinant (matrix F G m a c) m (width m a c)
def input (F G m a c : PTm n) : Fm PTm n := le one m ⋏ (rowShape F m c ⋏ rowShape G m a)
def coefficientSum (F G m a c s : PTm n) : PTm n := GaussianPolynomialDeterminant.coefficientSum
  (matrix F G m a c) m (width m a c) (Foundations.RuntimePermutationWords.count m) s
def valueSum (F G m a c x : PTm n) : PTm n := GaussianPolynomialDeterminant.valueSum
  (matrix F G m a c) m (width m a c) (Foundations.RuntimePermutationWords.count m) x

ipra_subst width
ipra_subst degreeBound
ipra_subst matrix
ipra_subst columns
ipra_subst norm
ipra_subst input
ipra_subst coefficientSum
ipra_subst valueSum

theorem matrix_row_cells (F G m a c r : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m a) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.rowCells (matrix F G m a c) m (width m a c) r := by
  refine .allI (.impI ?_)
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
    simpa only [Fm.shift,subst_rowShape,Syn.shift] using hG.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  simpa only [GaussianPolynomialDeterminantTerms.cell,Syn.shift,subst_matrix,subst_width,matrix,width,GaussianPolynomialMultiplicationMatrix.subst_matrix,GaussianPolynomialMultiplicationMatrix.subst_width] using
    GaussianPolynomialMultiplicationMatrix.matrix_polynomial_length (Syn.shift F) (Syn.shift G) (Syn.shift m)
      (Syn.shift a) (Syn.shift c) (Syn.shift r) (var 0) ms.wk gs.wk rs.wk Prf.hyp0

/-- All determinant shape hypotheses come from the actual original matrix
producer; no generated-table law is an input to the norm constructor. -/
theorem multiplication_table_shape (F G m a c : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.tableShape (matrix F G m a c) m (width m a c) := by
  refine .andI (GaussianPolynomialMultiplicationMatrix.matrix_length _ _ _ _ _) (.andI ?_ ?_)
  · refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_matrix,matrix,GaussianPolynomialMultiplicationMatrix.subst_matrix] using
      GaussianPolynomialMultiplicationMatrix.matrix_scalar_row_length (Syn.shift F) (Syn.shift G) (Syn.shift m)
        (Syn.shift a) (Syn.shift c) (var 0) Prf.hyp0
  · refine .allI (.impI ?_)
    have ms : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
      simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hm.shift
    have gs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift G) (Syn.shift m) (Syn.shift a) := by
      simpa only [Fm.shift,subst_rowShape,Syn.shift] using hG.shift
    simpa only [Syn.shift,subst_matrix,subst_width] using
      matrix_row_cells (Syn.shift F) (Syn.shift G) (Syn.shift m) (Syn.shift a) (Syn.shift c) (var 0) ms.wk gs.wk Prf.hyp0

theorem norm_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (norm F G m a c) ≐ succ (degreeBound m a c) :=
  GaussianPolynomialDeterminant.determinant_length _ _ _
theorem norm_canonical (F G m a c : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (norm F G m a c) :=
  GaussianPolynomialDeterminant.determinant_canonical _ _ _
theorem coefficient_leibniz (F G m a c s : PTm n) (hs : Γ ⊢[PRAAx] le s (degreeBound m a c)) : Γ ⊢[PRAAx]
    entry (norm F G m a c) s ≐ coefficientSum F G m a c s :=
  GaussianPolynomialDeterminant.coefficient_leibniz _ _ _ _ hs
theorem evaluation_leibniz (F G m a c x : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hG : Γ ⊢[PRAAx] rowShape G m a) : Γ ⊢[PRAAx] evaluate (norm F G m a c) x ≐ valueSum F G m a c x :=
  GaussianPolynomialDeterminant.evaluation_leibniz _ _ _ _ (multiplication_table_shape _ _ _ _ _ hm hG)

def certificate (F G m a c x : PTm n) : Fm PTm n := (length (norm F G m a c) ≐ succ (degreeBound m a c)) ⋏
  (canonicalCoefficients (norm F G m a c) ⋏
    (GaussianPolynomialDeterminantTerms.tableShape (matrix F G m a c) m (width m a c) ⋏
      (evaluate (norm F G m a c) x ≐ valueSum F G m a c x)))
ipra_subst certificate
theorem monic_norm (F G m a c x : PTm n) (h : Γ ⊢[PRAAx] input F G m a c) : Γ ⊢[PRAAx] certificate F G m a c x :=
  .andI (norm_length _ _ _ _ _) (.andI (norm_canonical _ _ _ _ _)
    (.andI (multiplication_table_shape _ _ _ _ _ (.andE₁ h) (.andE₂ (.andE₂ h)))
      (evaluation_leibniz _ _ _ _ _ _ (.andE₁ h) (.andE₂ (.andE₂ h)))))

theorem empty_evaluation (F G a c x : PTm n) : Γ ⊢[PRAAx] evaluate (norm F G zero a c) x ≐ qone :=
  GaussianPolynomialDeterminant.empty_evaluation _ _ _
theorem singleton_evaluation (F G a c x : PTm n) (hG : Γ ⊢[PRAAx] rowShape G one a) : Γ ⊢[PRAAx]
    evaluate (norm F G one a c) x ≐ evaluate (entry G zero) x := by
  have cell : Γ ⊢[PRAAx] GaussianPolynomialDeterminantTerms.cell (matrix F G one a c) zero zero ≐
      GaussianPolynomialMultiplicationMatrix.matrixEntry F G one a c zero zero :=
    GaussianPolynomialMultiplicationMatrix.matrix_coefficient_polynomial _ _ _ _ _ _ _ (le_refl one) (le_refl one)
  have slot : Γ ⊢[PRAAx] GaussianPolynomialMultiplicationMatrix.slot one zero ≐ zero := monus_self one
  have row : Γ ⊢[PRAAx] entry (GaussianPolynomialMultiplicationMatrix.stage F G one a c zero)
      (GaussianPolynomialMultiplicationMatrix.slot one zero) ≐ GaussianPolynomialMonicCompanion.normalizedRow (entry G zero) :=
    (entry_congr (GaussianPolynomialMultiplicationMatrix.stage_zero _ _ _ _ _) slot).eqTrans
      (GaussianPolynomialMultiplicationMatrix.normalized_rows_lookup G one zero (le_refl one))
  exact (GaussianPolynomialDeterminant.singleton_evaluation _ _ _ (multiplication_table_shape _ _ _ _ _ (le_refl one) hG)).eqTrans
    ((evaluate_congr cell (.eqRefl _)).eqTrans
      ((GaussianPolynomialMultiplicationMatrix.matrix_entry_evaluation _ _ _ _ _ _ _ _).eqTrans
        ((evaluate_congr row (.eqRefl _)).eqTrans (GaussianPolynomialMonicCompanion.normalized_evaluation _ _))))

/-! The constructor retains actual original companion columns and the whole
polynomial matrix. No numerical point is an input to this PR5 program. -/
def output (F G m a c : PTm n) : PTm n := pairT (norm F G m a c)
  (pairT (matrix F G m a c) (pairT (columns F G m a c) (width m a c)))
def normF : PR 5 := PTm.toPR (norm (var 0) (var 1) (var 2) (var 3) (var 4))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (F G m a c : PTm n) : PTm n := app outputF ![F,G,m,a,c]
ipra_subst output
ipra_subst run
theorem norm_program_at (F G m a c : PTm n) : Γ ⊢[PRAAx] app normF ![F,G,m,a,c] ≐ norm F G m a c := by
  simpa [normF] using toPR_eq (Γ := Γ) (norm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem program_at (F G m a c : PTm n) : Γ ⊢[PRAAx] run F G m a c ≐ output F G m a c := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![F,G,m,a,c]
theorem returned_norm (F G m a c : PTm n) : Γ ⊢[PRAAx] fstT (run F G m a c) ≐ norm F G m a c :=
  (program_at _ _ _ _ _).fstE
theorem returned_matrix (F G m a c : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run F G m a c)) ≐ matrix F G m a c :=
  (program_at _ _ _ _ _).sndE.fstE
theorem returned_columns (F G m a c : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run F G m a c))) ≐ columns F G m a c :=
  (program_at _ _ _ _ _).sndE.sndE.fstE
theorem returned_width (F G m a c : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run F G m a c))) ≐ width m a c :=
  (program_at _ _ _ _ _).sndE.sndE.sndE
theorem returned_length (F G m a c : PTm n) : Γ ⊢[PRAAx] length (fstT (run F G m a c)) ≐ succ (degreeBound m a c) :=
  (congrFst (returned_norm _ _ _ _ _)).eqTrans (norm_length _ _ _ _ _)
theorem returned_canonical (F G m a c : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (fstT (run F G m a c)) :=
  canonical_coefficients_congr (returned_norm _ _ _ _ _) (norm_canonical _ _ _ _ _)
theorem returned_coefficient (F G m a c s : PTm n) (hs : Γ ⊢[PRAAx] le s (degreeBound m a c)) : Γ ⊢[PRAAx]
    entry (fstT (run F G m a c)) s ≐ coefficientSum F G m a c s :=
  (entry_congr (returned_norm _ _ _ _ _) (.eqRefl _)).eqTrans (coefficient_leibniz _ _ _ _ _ _ hs)
theorem returned_evaluation (F G m a c x : PTm n) (h : Γ ⊢[PRAAx] input F G m a c) : Γ ⊢[PRAAx]
    evaluate (fstT (run F G m a c)) x ≐ valueSum F G m a c x :=
  (evaluate_congr (returned_norm _ _ _ _ _) (.eqRefl _)).eqTrans
    (evaluation_leibniz _ _ _ _ _ _ (.andE₁ h) (.andE₂ (.andE₂ h)))

/-! Curve action is retained on exactly the returned matrix. The vanishing
of these actual components is not yet a determinant-kernel theorem. -/
theorem returned_curve_action (F G m a c j x y : PTm n) (h : Γ ⊢[PRAAx] input F G m a c)
    (hj : Γ ⊢[PRAAx] lt j m) (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero) : Γ ⊢[PRAAx]
    GaussianPolynomialMultiplicationMatrix.pairing (fstT (sndT (run F G m a c))) m j x y ≐
      qmul (evaluate (values G m x) y) (GaussianRationalReciprocal.power y j) :=
  (GaussianPolynomialMultiplicationMatrix.pairing_congr _ _ _ _ (returned_matrix _ _ _ _ _)).eqTrans
    (GaussianPolynomialMultiplicationMatrix.evaluation_row _ _ _ _ _ _ _ _
      (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)) hj hCurve)
theorem returned_zero_action (F G m a c j x y : PTm n) (h : Γ ⊢[PRAAx] input F G m a c)
    (hj : Γ ⊢[PRAAx] lt j m) (hCurve : Γ ⊢[PRAAx] evaluate (monicValues F m x) y ≐ qzero)
    (hZero : Γ ⊢[PRAAx] evaluate (values G m x) y ≐ qzero) : Γ ⊢[PRAAx]
    GaussianPolynomialMultiplicationMatrix.pairing (fstT (sndT (run F G m a c))) m j x y ≐ qzero :=
  (GaussianPolynomialMultiplicationMatrix.pairing_congr _ _ _ _ (returned_matrix _ _ _ _ _)).eqTrans
    (GaussianPolynomialMultiplicationMatrix.zero_evaluation_row _ _ _ _ _ _ _ _
      (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)) hj hCurve hZero)


/-! Every original numerical size, coefficient code and query is bound in
these ordinary source endpoints. The curve equations are local point facts;
there is no supplied matrix kernel or norm-zero implication. -/
theorem actual_norm_table_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ rowShape (var 1) (var 2) (var 3) ⟶
      GaussianPolynomialDeterminantTerms.tableShape (matrix (var 0) (var 1) (var 2) (var 3) (var 4))
        (var 2) (width (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (multiplication_table_shape _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_monic_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (monic_norm _ _ _ _ _ _ Prf.hyp0))
theorem actual_monic_norm_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (degreeBound (var 2) (var 3) (var 4)) ⟶
      entry (norm (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5) ≐
        coefficientSum (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (coefficient_leibniz _ _ _ _ _ _ Prf.hyp0))
theorem actual_norm_programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((app normF ![var 0,var 1,var 2,var 3,var 4] ≐ norm (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.andI (norm_program_at _ _ _ _ _) (program_at _ _ _ _ _))
theorem returned_norm_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((length (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ succ (degreeBound (var 2) (var 3) (var 4))) ⋏
      canonicalCoefficients (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.andI (returned_length _ _ _ _ _) (returned_canonical _ _ _ _ _))
theorem returned_norm_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ norm (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ matrix (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        ((fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ columns (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
          (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐ width (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.andI (returned_norm _ _ _ _ _) (.andI (returned_matrix _ _ _ _ _)
    (.andI (returned_columns _ _ _ _ _) (returned_width _ _ _ _ _))))
theorem returned_norm_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le (var 5) (degreeBound (var 2) (var 3) (var 4)) ⟶
      entry (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 5) ≐
        coefficientSum (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (returned_coefficient _ _ _ _ _ _ Prf.hyp0))
theorem returned_norm_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      evaluate (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 5) ≐
        valueSum (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (returned_evaluation _ _ _ _ _ _ Prf.hyp0))
theorem empty_and_singleton_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((evaluate (norm (var 0) (var 1) zero (var 2) (var 3)) (var 4) ≐ qone) ⋏
      (rowShape (var 1) one (var 2) ⟶ evaluate (norm (var 0) (var 1) one (var 2) (var 3)) (var 4) ≐
        evaluate (entry (var 1) zero) (var 4))) :=
  closeUniv 5 (.andI (empty_evaluation _ _ _ _ _) (.impI (singleton_evaluation _ _ _ _ _ Prf.hyp0)))
theorem returned_curve_action_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (var 2) ⟶
      evaluate (monicValues (var 0) (var 2) (var 6)) (var 7) ≐ qzero ⟶
        GaussianPolynomialMultiplicationMatrix.pairing (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
          (var 2) (var 5) (var 6) (var 7) ≐ qmul (evaluate (values (var 1) (var 2) (var 6)) (var 7))
            (GaussianRationalReciprocal.power (var 7) (var 5))) :=
  closeUniv 8 (.impI (.impI (.impI (returned_curve_action _ _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem returned_zero_action_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (var 2) ⟶
      evaluate (monicValues (var 0) (var 2) (var 6)) (var 7) ≐ qzero ⟶
        evaluate (values (var 1) (var 2) (var 6)) (var 7) ≐ qzero ⟶
          GaussianPolynomialMultiplicationMatrix.pairing (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))
            (var 2) (var 5) (var 6) (var 7) ≐ qzero) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (returned_zero_action _ _ _ _ _ _ _ _ hyp2.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialMonicNorm
