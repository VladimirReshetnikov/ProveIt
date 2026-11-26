import IPRADerivations.Analysis.LinearAlgebra.GaussianScalarIdentityDeterminant
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalFiberRightInverse
import IPRADerivations.Analysis.LinearAlgebra.GaussianScalarDeterminantMultiplication

/-!
# The determinant of the actual completed fiber table is nonzero

The existing numerical W and Z are used without changing their entries or
their matrix-product program. Their proved right-inverse entries imply
that the determinant of WZ is one. The constant-polynomial table WP has
the same determinant value and its single stored coefficient records that
value. The original curve consumer retains the actual ordinate list,
selected abscissa and exact partition total.

No Vandermonde product formula, determinant premise, or norm multiplicity
claim is supplied. All dimensions, lists and source data are numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFiberDeterminantNonzero

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qmul_congr qmul_zero_left canonical_coefficient_at)
open LeanProofs.IPRA.Analysis.GaussianScalarDeterminant (scalarDet)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (W WP)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberRightInverse (Z)
open LeanProofs.IPRA.Analysis.GaussianRationalMatrixFiniteSums (matrixProduct)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def polynomial (R m : PTm n) : PTm n := GaussianPolynomialDeterminant.determinant (WP R m) m zero
def determinant (R m : PTm n) : PTm n := scalarDet (W R m) m

@[simp] theorem subst_polynomial {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (polynomial R m) = polynomial (Syn.subst σ R) (Syn.subst σ m) := by simp [polynomial]
@[simp] theorem subst_determinant {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (determinant R m) = determinant (Syn.subst σ R) (Syn.subst σ m) := by simp [determinant]

theorem product_identity_entries (R m : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    GaussianScalarIdentityDeterminant.identityEntries (matrixProduct (W R m) (Z R m) m) m := by
  simpa only [GaussianScalarIdentityDeterminant.identityEntries,GaussianScalarIdentityDeterminant.identityRow,
    GaussianRationalFiberRightInverse.identityTable,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,
    GaussianPolynomialDeterminantTerms.subst_cell] using
      GaussianRationalFiberRightInverse.right_inverse R m hDistinct hSize

theorem product_determinant_one (R m : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    scalarDet (matrixProduct (W R m) (Z R m) m) m ≐ qone :=
  GaussianScalarIdentityDeterminant.identity_det_of_entries _ _ (product_identity_entries _ _ hDistinct hSize)

theorem polynomial_length (R m : PTm n) : Γ ⊢[PRAAx] length (polynomial R m) ≐ one :=
  (GaussianPolynomialDeterminant.determinant_length _ _ _).eqTrans (congrSucc (mul_zero _))
theorem polynomial_canonical (R m : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalSyntheticDivision.canonicalCoefficients (polynomial R m) :=
  GaussianPolynomialDeterminant.determinant_canonical _ _ _

theorem polynomial_evaluation (R m z : PTm n) : Γ ⊢[PRAAx]
    evaluate (polynomial R m) z ≐ determinant R m := by
  have values : Γ ⊢[PRAAx] GaussianScalarDeterminant.cellValuesEqual (WP R m)
      (GaussianScalarDeterminant.constantTable (W R m) m) m z qzero := by
    refine .allI (.impI (.allI (.impI ?_)))
    let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
    have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
    have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
      simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
    have jj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := Prf.hyp0
    have e := (GaussianScalarDeterminant.constant_cell_evaluation (Γ := Δ)
      (W (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift m))) (Syn.shift (Syn.shift m)) (var 1) (var 0) qzero rr jj).eqTrans
        ((GaussianTranslatedNonconstant.recode_eq _ (GaussianRationalFiberVandermonde.W_canonical _ _ _ _ rr jj)).eqTrans
          (GaussianRationalFiberVandermonde.W_lookup _ _ _ _ rr jj))
    have left := GaussianRationalFiberVandermonde.WP_evaluation (Γ := Δ)
      (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift m)) (var 1) (var 0) (Syn.shift (Syn.shift z)) rr jj
    simpa only [Δ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,GaussianRationalFiberVandermonde.subst_W,
      GaussianRationalFiberVandermonde.subst_WP,GaussianScalarDeterminant.subst_constantTable,
      GaussianRationalHorner.subst_qzero] using left.eqTrans e.eqSymm
  exact GaussianScalarDeterminant.determinant_evaluation_congr _ _ _ _ _ _ _
    (GaussianRationalFiberVandermonde.WP_shape _ _) (GaussianScalarDeterminant.constant_shape _ _) values

theorem polynomial_coefficient (R m : PTm n) : Γ ⊢[PRAAx]
    entry (polynomial R m) zero ≐ determinant R m := by
  have canon : Γ ⊢[PRAAx] canonical (entry (polynomial R m) zero) :=
    canonical_coefficient_at _ _ (polynomial_canonical _ _)
      (lt_congr (.eqRefl _) (polynomial_length _ _).eqSymm (le_refl one))
  have first := (congrAp3 GaussianRationalHorner.hornerF (polynomial_length R m) (.eqRefl (polynomial R m)) (.eqRefl qzero)).eqTrans
    ((GaussianRationalSyntheticDivision.first_prefix _ _).eqTrans (GaussianRationalSyntheticDivision.qzero_add _ canon))
  exact first.eqSymm.eqTrans (polynomial_evaluation R m qzero)

/-! The existing full inverse run is retained in the first field. -/
def output (R m : PTm n) : PTm n := pairT (GaussianRationalFiberRightInverse.run R m)
  (pairT (determinant R m) (pairT (scalarDet (Z R m) m)
    (pairT (polynomial R m) (entry (polynomial R m) zero))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (R m : PTm n) : PTm n := ap2 outputF R m
def inverseField (c : PTm n) : PTm n := fstT c
def determinantField (c : PTm n) : PTm n := fstT (sndT c)
def inverseDeterminantField (c : PTm n) : PTm n := fstT (sndT (sndT c))
def polynomialField (c : PTm n) : PTm n := fstT (sndT (sndT (sndT c)))
def coefficientField (c : PTm n) : PTm n := sndT (sndT (sndT (sndT c)))
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (output R m) = output (Syn.subst σ R) (Syn.subst σ m) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (run R m) = run (Syn.subst σ R) (Syn.subst σ m) := by simp [run]
@[simp] theorem subst_inverseField {l : ℕ} (σ : Fin n → PTm l) (c : PTm n) :
    Syn.subst σ (inverseField c) = inverseField (Syn.subst σ c) := by simp [inverseField]
@[simp] theorem subst_determinantField {l : ℕ} (σ : Fin n → PTm l) (c : PTm n) :
    Syn.subst σ (determinantField c) = determinantField (Syn.subst σ c) := by simp [determinantField]
@[simp] theorem subst_inverseDeterminantField {l : ℕ} (σ : Fin n → PTm l) (c : PTm n) :
    Syn.subst σ (inverseDeterminantField c) = inverseDeterminantField (Syn.subst σ c) := by simp [inverseDeterminantField]
@[simp] theorem subst_polynomialField {l : ℕ} (σ : Fin n → PTm l) (c : PTm n) :
    Syn.subst σ (polynomialField c) = polynomialField (Syn.subst σ c) := by simp [polynomialField]
@[simp] theorem subst_coefficientField {l : ℕ} (σ : Fin n → PTm l) (c : PTm n) :
    Syn.subst σ (coefficientField c) = coefficientField (Syn.subst σ c) := by simp [coefficientField]

theorem program_at (R m : PTm n) : Γ ⊢[PRAAx] run R m ≐ output R m := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![R,m]
theorem returned_inverse (R m : PTm n) : Γ ⊢[PRAAx]
    inverseField (run R m) ≐ GaussianRationalFiberRightInverse.run R m :=
  (congrFst (program_at _ _)).eqTrans (fst_pair _ _)
theorem returned_determinant (R m : PTm n) : Γ ⊢[PRAAx] determinantField (run R m) ≐ determinant R m :=
  (congrFst ((congrSnd (program_at _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_inverse_determinant (R m : PTm n) : Γ ⊢[PRAAx]
    inverseDeterminantField (run R m) ≐ scalarDet (Z R m) m := by
  have tail := (congrSnd ((congrSnd (program_at (Γ := Γ) R m)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
  exact (congrFst tail).eqTrans (fst_pair _ _)
theorem returned_polynomial (R m : PTm n) : Γ ⊢[PRAAx] polynomialField (run R m) ≐ polynomial R m := by
  have tail := (congrSnd ((congrSnd ((congrSnd (program_at (Γ := Γ) R m)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
  exact (congrFst tail).eqTrans (fst_pair _ _)
theorem returned_coefficient (R m : PTm n) : Γ ⊢[PRAAx] coefficientField (run R m) ≐ entry (polynomial R m) zero := by
  have tail := (congrSnd ((congrSnd ((congrSnd (program_at (Γ := Γ) R m)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
  exact (congrSnd tail).eqTrans (snd_pair _ _)
theorem returned_coefficient_value (R m : PTm n) : Γ ⊢[PRAAx]
    coefficientField (run R m) ≐ determinantField (run R m) :=
  (returned_coefficient _ _).eqTrans ((polynomial_coefficient _ _).eqTrans (returned_determinant _ _).eqSymm)

def sourceOutput (L p g m : PTm n) : PTm n := pairT (run (GaussianRationalCurveFibers.yList L p g) m)
  (pairT (GaussianRationalCurveFibers.selectedX L p g) (GaussianRationalFiberGrouping.partitionTotal L p))
def sourceF : PR 4 := PTm.toPR (sourceOutput (var 0) (var 1) (var 2) (var 3))
def sourceRun (L p g m : PTm n) : PTm n := app sourceF ![L,p,g,m]
@[simp] theorem subst_sourceOutput {l : ℕ} (σ : Fin n → PTm l) (L p g m : PTm n) :
    Syn.subst σ (sourceOutput L p g m) = sourceOutput (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) (Syn.subst σ m) := by simp [sourceOutput]
@[simp] theorem subst_sourceRun {l : ℕ} (σ : Fin n → PTm l) (L p g m : PTm n) :
    Syn.subst σ (sourceRun L p g m) = sourceRun (Syn.subst σ L) (Syn.subst σ p) (Syn.subst σ g) (Syn.subst σ m) := by
  simp only [sourceRun,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem source_program_at (L p g m : PTm n) : Γ ⊢[PRAAx] sourceRun L p g m ≐ sourceOutput L p g m := by
  simpa [sourceRun,sourceF] using toPR_eq (Γ := Γ) (sourceOutput (var 0) (var 1) (var 2) (var 3) : PTm 4) ![L,p,g,m]
theorem source_returned_generic (L p g m : PTm n) : Γ ⊢[PRAAx]
    fstT (sourceRun L p g m) ≐ run (GaussianRationalCurveFibers.yList L p g) m :=
  (congrFst (source_program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem source_returned_x (L p g m : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sourceRun L p g m)) ≐ GaussianRationalCurveFibers.selectedX L p g :=
  (congrFst ((congrSnd (source_program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem source_returned_partition (L p g m : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sourceRun L p g m)) ≐ length L :=
  ((congrSnd ((congrSnd (source_program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)).eqTrans
    (GaussianRationalFiberGrouping.cardinal_partition _ _)

theorem determinant_inverse (R m : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    qmul (determinant R m) (scalarDet (Z R m) m) ≐ qone :=
  (GaussianScalarDeterminantMultiplication.scalar_det_multiply _ _ _).eqSymm.eqTrans
    (product_determinant_one _ _ hDistinct hSize)

theorem determinant_nonzero (R m : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx] neg (determinant R m ≐ qzero) := by
  refine .impI ?_
  have inverse := determinant_inverse (Γ := (determinant R m ≐ qzero) :: Γ) R m hDistinct.wk hSize.wk
  have zeroProduct : (determinant R m ≐ qzero) :: Γ ⊢[PRAAx]
      qmul (determinant R m) (scalarDet (Z R m) m) ≐ qzero :=
    (qmul_congr Prf.hyp0 (.eqRefl _)).eqTrans (qmul_zero_left _)
  exact .impE GaussianRationalCurveFibers.gaussian_one_nonzero (inverse.eqSymm.eqTrans zeroProduct)

theorem nonzero_congr {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ r)
    (hr : Γ ⊢[PRAAx] neg (r ≐ qzero)) : Γ ⊢[PRAAx] neg (q ≐ qzero) :=
  .impI (.impE hr.wk (h.wk.eqSymm.eqTrans Prf.hyp0))
theorem polynomial_coefficient_nonzero (R m : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    neg (entry (polynomial R m) zero ≐ qzero) :=
  nonzero_congr (polynomial_coefficient _ _) (determinant_nonzero _ _ hDistinct hSize)
theorem polynomial_evaluation_nonzero (R m z : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    neg (evaluate (polynomial R m) z ≐ qzero) :=
  nonzero_congr (polynomial_evaluation _ _ _) (determinant_nonzero _ _ hDistinct hSize)

def certificate (R m : PTm n) : Fm PTm n :=
  (scalarDet (matrixProduct (W R m) (Z R m) m) m ≐ qone) ⋏
    ((qmul (determinant R m) (scalarDet (Z R m) m) ≐ qone) ⋏
      (neg (determinant R m ≐ qzero) ⋏ ((length (polynomial R m) ≐ one) ⋏
        ((entry (polynomial R m) zero ≐ determinant R m) ⋏ neg (entry (polynomial R m) zero ≐ qzero)))))
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    (certificate R m).subst σ = certificate (Syn.subst σ R) (Syn.subst σ m) := by simp [certificate]
theorem determinant_correct (R m : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx] certificate R m :=
  .andI (product_determinant_one _ _ hDistinct hSize)
    (.andI (determinant_inverse _ _ hDistinct hSize) (.andI (determinant_nonzero _ _ hDistinct hSize)
      (.andI (polynomial_length _ _) (.andI (polynomial_coefficient _ _) (polynomial_coefficient_nonzero _ _ hDistinct hSize)))))

theorem returned_inverse_value (R m : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx]
    qmul (determinantField (run R m)) (inverseDeterminantField (run R m)) ≐ qone :=
  (qmul_congr (returned_determinant _ _) (returned_inverse_determinant _ _)).eqTrans (determinant_inverse _ _ hDistinct hSize)
theorem returned_nonzero (R m : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx] neg (determinantField (run R m) ≐ qzero) :=
  nonzero_congr (returned_determinant _ _) (determinant_nonzero _ _ hDistinct hSize)
theorem returned_coefficient_nonzero (R m : PTm n)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m) : Γ ⊢[PRAAx] neg (coefficientField (run R m) ≐ qzero) :=
  nonzero_congr (returned_coefficient _ _) (polynomial_coefficient_nonzero _ _ hDistinct hSize)

theorem source_correct (F m L p g : PTm n)
    (hCurve : Γ ⊢[PRAAx] GaussianRationalCurveFibers.curveZeros F m L)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct L) : Γ ⊢[PRAAx]
    certificate (GaussianRationalCurveFibers.yList L p g) m :=
  determinant_correct _ _ (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ hDistinct)
    (GaussianRationalFiberRightInverse.source_size_bound _ _ _ _ _ hCurve hDistinct)
theorem source_nonzero (F m L p g : PTm n)
    (hCurve : Γ ⊢[PRAAx] GaussianRationalCurveFibers.curveZeros F m L)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct L) : Γ ⊢[PRAAx]
    neg (determinant (GaussianRationalCurveFibers.yList L p g) m ≐ qzero) :=
  determinant_nonzero _ _ (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ hDistinct)
    (GaussianRationalFiberRightInverse.source_size_bound _ _ _ _ _ hCurve hDistinct)
theorem source_returned_nonzero (F m L p g : PTm n)
    (hCurve : Γ ⊢[PRAAx] GaussianRationalCurveFibers.curveZeros F m L)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct L) : Γ ⊢[PRAAx]
    neg (determinantField (fstT (sourceRun L p g m)) ≐ qzero) :=
  nonzero_congr (congrFst (congrSnd (source_returned_generic _ _ _ _)))
    (returned_nonzero _ _ (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ hDistinct)
      (GaussianRationalFiberRightInverse.source_size_bound _ _ _ _ _ hCurve hDistinct))
theorem source_returned_coefficient_nonzero (F m L p g : PTm n)
    (hCurve : Γ ⊢[PRAAx] GaussianRationalCurveFibers.curveZeros F m L)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalCurveFibers.pointDistinct L) : Γ ⊢[PRAAx]
    neg (coefficientField (fstT (sourceRun L p g m)) ≐ qzero) :=
  nonzero_congr (congrSnd (congrSnd (congrSnd (congrSnd (source_returned_generic _ _ _ _)))))
    (returned_coefficient_nonzero _ _ (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ hDistinct)
      (GaussianRationalFiberRightInverse.source_size_bound _ _ _ _ _ hCurve hDistinct))

/-! All list codes, dimensions, original curve data and source indices
are bound in ordinary PRA proofs, including the empty table and fiber. -/
theorem product_determinant_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ le (length (var 0)) (var 1) ⟶
      scalarDet (matrixProduct (W (var 0) (var 1)) (Z (var 0) (var 1)) (var 1)) (var 1) ≐ qone) :=
  closeUniv 2 (.impI (.impI (product_determinant_one _ _ Prf.hyp1 Prf.hyp0)))
theorem determinant_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ le (length (var 0)) (var 1) ⟶ neg (determinant (var 0) (var 1) ≐ qzero)) :=
  closeUniv 2 (.impI (.impI (determinant_nonzero _ _ Prf.hyp1 Prf.hyp0)))
theorem constant_polynomial_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (polynomial (var 0) (var 1)) ≐ one) ⋏ (entry (polynomial (var 0) (var 1)) zero ≐ determinant (var 0) (var 1))) :=
  closeUniv 2 (.andI (polynomial_length _ _) (polynomial_coefficient _ _))
theorem constant_polynomial_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ le (length (var 0)) (var 1) ⟶
      neg (evaluate (polynomial (var 0) (var 1)) (var 2) ≐ qzero)) :=
  closeUniv 3 (.impI (.impI (polynomial_evaluation_nonzero _ _ _ Prf.hyp1 Prf.hyp0)))
theorem determinant_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ le (length (var 0)) (var 1) ⟶ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (.impI (determinant_correct _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run (var 0) (var 1) ≐ output (var 0) (var 1)) ⋏
      (inverseField (run (var 0) (var 1)) ≐ GaussianRationalFiberRightInverse.run (var 0) (var 1))) :=
  closeUniv 2 (.andI (program_at _ _) (returned_inverse _ _))
theorem returned_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalFiniteRoots.distinct (var 0) ⟶ le (length (var 0)) (var 1) ⟶
      (neg (determinantField (run (var 0) (var 1)) ≐ qzero) ⋏ neg (coefficientField (run (var 0) (var 1)) ≐ qzero))) :=
  closeUniv 2 (.impI (.impI (.andI (returned_nonzero _ _ Prf.hyp1 Prf.hyp0) (returned_coefficient_nonzero _ _ Prf.hyp1 Prf.hyp0))))
theorem original_fiber_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalCurveFibers.curveZeros (var 0) (var 1) (var 2) ⟶ GaussianRationalCurveFibers.pointDistinct (var 2) ⟶
      certificate (GaussianRationalCurveFibers.yList (var 2) (var 3) (var 4)) (var 1)) :=
  closeUniv 5 (.impI (.impI (source_correct _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem source_fields_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (sourceRun (var 0) (var 1) (var 2) (var 3)) ≐ run (GaussianRationalCurveFibers.yList (var 0) (var 1) (var 2)) (var 3)) ⋏
      ((fstT (sndT (sourceRun (var 0) (var 1) (var 2) (var 3))) ≐ GaussianRationalCurveFibers.selectedX (var 0) (var 1) (var 2)) ⋏
        (sndT (sndT (sourceRun (var 0) (var 1) (var 2) (var 3))) ≐ length (var 0)))) :=
  closeUniv 4 (.andI (source_returned_generic _ _ _ _) (.andI (source_returned_x _ _ _ _) (source_returned_partition _ _ _ _)))
theorem returned_original_fiber_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianRationalCurveFibers.curveZeros (var 0) (var 1) (var 2) ⟶ GaussianRationalCurveFibers.pointDistinct (var 2) ⟶
      (neg (determinantField (fstT (sourceRun (var 2) (var 3) (var 4) (var 1))) ≐ qzero) ⋏
        neg (coefficientField (fstT (sourceRun (var 2) (var 3) (var 4) (var 1))) ≐ qzero))) :=
  closeUniv 5 (.impI (.impI (.andI (source_returned_nonzero _ _ _ _ _ Prf.hyp1 Prf.hyp0)
    (source_returned_coefficient_nonzero _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianFiberDeterminantNonzero
