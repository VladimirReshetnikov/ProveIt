import IPRADerivations.Analysis.GaussianFiberDeterminantNonzero
import IPRADerivations.Analysis.GaussianPolynomialScalarLeftDeterminant
import IPRADerivations.Analysis.GaussianPolynomialRowFactorDeterminant
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual local fiber divisibility of the original norm polynomial

The existing WZ right inverse provides a computed inverse scalar det Z.
Scaling the actual row-quotient determinant by this scalar removes det W
from the determinant factorization. The actual padded original norm and
the actual repeated-root product then agree on the finite numerical grid,
which derives bounded equality of their stored coefficients.

The source theorem assumes only the original norm shape and distinct
common-zero predicates. Its fiber size, ordinate distinction, row zeros
and inverse scalar law are derived. No nonzero norm is needed locally.
Accumulation over different fibers and the sharp total degree bound are
separate obligations. Every size, code, count and source index is numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNormFiberDivisibility

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power)
open LeanProofs.IPRA.Analysis.GaussianRationalCoefficientScaling (scaled scaled_length evaluation_linearity)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminant (determinant determinant_length determinant_canonical)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (tableShape)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (W WM firstRowsZero)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberRightInverse (Z)
open LeanProofs.IPRA.Analysis.GaussianScalarDeterminant (scalarDet)
open LeanProofs.IPRA.Analysis.GaussianPolynomialRowQuotient (H)
open LeanProofs.IPRA.Analysis.GaussianRationalGridCoefficientEquality (gridEqual coefficientsEqual)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteGridIdentity (gridPoint)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseScalar (R m : PTm n) : PTm n := scalarDet (Z R m) m
def quotientDeterminant (R M m B t x : PTm n) : PTm n :=
  GaussianPolynomialRowFactorDeterminant.quotientDeterminant (WM R M m B) m B t x
def quotient (R M m B t x : PTm n) : PTm n := scaled (quotientDeterminant R M m B t x) (inverseScalar R m)
def width (m B t : PTm n) : PTm n := t+m*B
def paddedOriginal (M m B t : PTm n) : PTm n := leftPad (determinant M m B) t
def factorProduct (R M m B t x : PTm n) : PTm n :=
  GaussianRationalPolynomialProduct.product (H x t) (quotient R M m B t x) t (m*B)

@[simp] theorem subst_inverseScalar {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (inverseScalar R m) = inverseScalar (Syn.subst σ R) (Syn.subst σ m) := by simp [inverseScalar]
@[simp] theorem subst_quotientDeterminant {l : ℕ} (σ : Fin n → PTm l) (R M m B t x : PTm n) :
    Syn.subst σ (quotientDeterminant R M m B t x) = quotientDeterminant (Syn.subst σ R) (Syn.subst σ M)
      (Syn.subst σ m) (Syn.subst σ B) (Syn.subst σ t) (Syn.subst σ x) := by simp [quotientDeterminant]
@[simp] theorem subst_quotient {l : ℕ} (σ : Fin n → PTm l) (R M m B t x : PTm n) :
    Syn.subst σ (quotient R M m B t x) = quotient (Syn.subst σ R) (Syn.subst σ M)
      (Syn.subst σ m) (Syn.subst σ B) (Syn.subst σ t) (Syn.subst σ x) := by simp [quotient]
@[simp] theorem subst_width {l : ℕ} (σ : Fin n → PTm l) (m B t : PTm n) :
    Syn.subst σ (width m B t) = width (Syn.subst σ m) (Syn.subst σ B) (Syn.subst σ t) := by simp [width]
@[simp] theorem subst_paddedOriginal {l : ℕ} (σ : Fin n → PTm l) (M m B t : PTm n) :
    Syn.subst σ (paddedOriginal M m B t) = paddedOriginal (Syn.subst σ M) (Syn.subst σ m)
      (Syn.subst σ B) (Syn.subst σ t) := by simp [paddedOriginal]
@[simp] theorem subst_factorProduct {l : ℕ} (σ : Fin n → PTm l) (R M m B t x : PTm n) :
    Syn.subst σ (factorProduct R M m B t x) = factorProduct (Syn.subst σ R) (Syn.subst σ M)
      (Syn.subst σ m) (Syn.subst σ B) (Syn.subst σ t) (Syn.subst σ x) := by simp [factorProduct]

theorem multiply_inverse_cancel (a b c : PTm n) (hInverse : Γ ⊢[PRAAx] qmul a b ≐ qone)
    (hCanonical : Γ ⊢[PRAAx] canonical c) : Γ ⊢[PRAAx] qmul b (qmul a c) ≐ c :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
      ((qmul_congr hInverse (.eqRefl _)).eqTrans (GaussianPolynomialDeterminantTerms.one_mul_canonical _ hCanonical)))
theorem multiply_exchange (a b c : PTm n) : Γ ⊢[PRAAx]
    qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
      (GaussianReciprocalHorner.qmul_associative _ _ _))

theorem quotient_length (R M m B t x : PTm n) : Γ ⊢[PRAAx]
    length (quotient R M m B t x) ≐ succ (m*B) :=
  (scaled_length _ _).eqTrans (GaussianPolynomialRowFactorDeterminant.quotient_length _ _ _ _ _)
theorem quotient_canonical (R M m B t x : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (quotient R M m B t x) := GaussianPolynomialScalarLeftDeterminant.scaled_canonical _ _
theorem padded_length (M m B t : PTm n) : Γ ⊢[PRAAx] length (paddedOriginal M m B t) ≐ succ (width m B t) :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (determinant_length _ _ _)).eqTrans (by unfold width; ipra_ring))
theorem padded_canonical (M m B t : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (paddedOriginal M m B t) :=
  GaussianPolynomialMonicCompanion.pad_canonical _ _ (determinant_canonical _ _ _)
theorem product_length (R M m B t x : PTm n) : Γ ⊢[PRAAx]
    length (factorProduct R M m B t x) ≐ succ (width m B t) :=
  GaussianRationalPolynomialProduct.product_length _ _ _ _
theorem product_canonical (R M m B t x : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (factorProduct R M m B t x) := GaussianRationalPolynomialProduct.product_canonical _ _ _ _

/-- The inverse and row-zero guards are local data contracts here. The
original-source consumer below derives all of them. -/
theorem evaluation_factor (R M m B t x z : PTm n)
    (hM : Γ ⊢[PRAAx] tableShape M m B)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m)
    (hRoots : Γ ⊢[PRAAx] firstRowsZero (WM R M m B) m t x)
    (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    evaluate (determinant M m B) z ≐ qmul (power (qsub z x) t) (evaluate (quotient R M m B t x) z) := by
  have left := GaussianPolynomialScalarLeftDeterminant.WM_evaluation (Γ := Γ) R M m B z hM
  have right := GaussianPolynomialRowFactorDeterminant.determinant_evaluation (Γ := Γ)
    (WM R M m B) m B t x z (GaussianRationalFiberVandermonde.product_shape _ _ _ _) hRoots ht
  have inverse := GaussianFiberDeterminantNonzero.determinant_inverse (Γ := Γ) R m hDistinct hSize
  have cancel := multiply_inverse_cancel (Γ := Γ) (scalarDet (W R m) m) (inverseScalar R m)
    (evaluate (determinant M m B) z) inverse (GaussianRationalHorner.horner_canonical _ _ _)
  have scaled : Γ ⊢[PRAAx]
      qmul (inverseScalar R m) (qmul (scalarDet (W R m) m) (evaluate (determinant M m B) z)) ≐
        qmul (inverseScalar R m) (qmul (power (qsub z x) t) (evaluate (quotientDeterminant R M m B t x) z)) :=
    qmul_congr (.eqRefl _) (left.eqSymm.eqTrans right)
  exact cancel.eqSymm.eqTrans (scaled.eqTrans ((multiply_exchange _ _ _).eqTrans
    (qmul_congr (.eqRefl _) (evaluation_linearity _ _ _).eqSymm)))

theorem buffer_evaluation (R M m B t x z : PTm n)
    (hM : Γ ⊢[PRAAx] tableShape M m B)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m)
    (hRoots : Γ ⊢[PRAAx] firstRowsZero (WM R M m B) m t x)
    (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    evaluate (paddedOriginal M m B t) z ≐ evaluate (factorProduct R M m B t x) z :=
  (pad_evaluation _ _ _).eqTrans ((evaluation_factor _ _ _ _ _ _ _ hM hDistinct hSize hRoots ht).eqTrans
    (((GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _ (GaussianPolynomialRowQuotient.H_length _ _)
      (quotient_length _ _ _ _ _ _)).eqTrans (qmul_congr (GaussianPolynomialRowQuotient.H_evaluation _ _ _) (.eqRefl _))).eqSymm))

theorem buffer_grid_equal (R M m B t x : PTm n)
    (hM : Γ ⊢[PRAAx] tableShape M m B)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m)
    (hRoots : Γ ⊢[PRAAx] firstRowsZero (WM R M m B) m t x)
    (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    gridEqual (paddedOriginal M m B t) (factorProduct R M m B t x) (width m B t) := by
  have ms : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift M) (Syn.shift m) (Syn.shift B) := by
    simpa only [Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using hM.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalFiniteRoots.distinct (Syn.shift R) := by
    simpa only [Fm.shift,GaussianRationalFiniteRoots.subst_distinct,Syn.shift] using hDistinct.shift
  have sizes : Γ.map Fm.shift ⊢[PRAAx] le (length (Syn.shift R)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,subst_length,Syn.shift] using hSize.shift
  have roots : Γ.map Fm.shift ⊢[PRAAx] firstRowsZero
      (WM (Syn.shift R) (Syn.shift M) (Syn.shift m) (Syn.shift B)) (Syn.shift m) (Syn.shift t) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRationalFiberVandermonde.subst_firstRowsZero,
      GaussianRationalFiberVandermonde.subst_WM,Syn.shift] using hRoots.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift t) (Syn.shift m) := by
    simpa only [Fm.shift,subst_le,Syn.shift] using ht.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_paddedOriginal,subst_factorProduct,subst_width] using
    buffer_evaluation (Syn.shift R) (Syn.shift M) (Syn.shift m) (Syn.shift B) (Syn.shift t) (Syn.shift x)
      (gridPoint (var 0)) ms.wk ds.wk sizes.wk roots.wk ts.wk

theorem coefficients_factor (R M m B t x : PTm n)
    (hM : Γ ⊢[PRAAx] tableShape M m B)
    (hDistinct : Γ ⊢[PRAAx] GaussianRationalFiniteRoots.distinct R)
    (hSize : Γ ⊢[PRAAx] le (length R) m)
    (hRoots : Γ ⊢[PRAAx] firstRowsZero (WM R M m B) m t x)
    (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    coefficientsEqual (paddedOriginal M m B t) (factorProduct R M m B t x) (width m B t) :=
  GaussianRationalGridCoefficientEquality.coefficients_equal _ _ _ (padded_length _ _ _ _) (product_length _ _ _ _ _ _)
    (padded_canonical _ _ _ _) (product_canonical _ _ _ _ _ _) (buffer_grid_equal _ _ _ _ _ _ hM hDistinct hSize hRoots ht)

theorem coefficients_at (C D N i : PTm n) (h : Γ ⊢[PRAAx] coefficientsEqual C D N)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] entry C i ≐ entry D i := by
  have rule : Γ ⊢[PRAAx] le i N ⟶ entry C i ≐ entry D i := by
    simpa [GaussianRationalGridCoefficientEquality.coefficientsEqual] using h.allE i
  exact .impE rule hi
theorem coefficients_left_congr {C C' D N : PTm n} (hc : Γ ⊢[PRAAx] C ≐ C')
    (h : Γ ⊢[PRAAx] coefficientsEqual C D N) : Γ ⊢[PRAAx] coefficientsEqual C' D N := by
  simpa only [GaussianRationalGridCoefficientEquality.subst_coefficientsEqual,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (coefficientsEqual (var 0) (var 1) (var 2) : Fm PTm 3)
        ![C,D,N] ![C',D,N] (fun i => by fin_cases i; exact hc; exact .eqRefl _; exact .eqRefl _)
        (by simpa only [GaussianRationalGridCoefficientEquality.subst_coefficientsEqual,Syn.subst_var,
          Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h)
theorem pad_congr {C D t u : PTm n} (hc : Γ ⊢[PRAAx] C ≐ D) (ht : Γ ⊢[PRAAx] t ≐ u) : Γ ⊢[PRAAx]
    leftPad C t ≐ leftPad D u := by
  ipra_congr (leftPad (var 0) (var 1) : PTm 2) with [hc, ht]

/-! Original source aliases use the existing returned norm matrix and
the original grouping. No second ordinate-list producer is introduced. -/
def sourceQuotient (F G m a c P p g : PTm n) : PTm n := quotient
  (GaussianRationalCurveFibers.yList P p g) (GaussianRationalFiberVandermonde.sourceMatrix F G m a c)
  m (GaussianPolynomialMonicNorm.width m a c) (GaussianRationalFiberGrouping.fiberCount P p g)
  (GaussianRationalCurveFibers.selectedX P p g)
def sourceOriginal (F G m a c : PTm n) : PTm n := fstT (GaussianPolynomialMonicNorm.run F G m a c)
def sourcePadded (F G m a c P p g : PTm n) : PTm n :=
  leftPad (sourceOriginal F G m a c) (GaussianRationalFiberGrouping.fiberCount P p g)
def sourceFactor (F G m a c P p g : PTm n) : PTm n := factorProduct
  (GaussianRationalCurveFibers.yList P p g) (GaussianRationalFiberVandermonde.sourceMatrix F G m a c)
  m (GaussianPolynomialMonicNorm.width m a c) (GaussianRationalFiberGrouping.fiberCount P p g)
  (GaussianRationalCurveFibers.selectedX P p g)
def sourceWidth (m a c P p g : PTm n) : PTm n := width m (GaussianPolynomialMonicNorm.width m a c)
  (GaussianRationalFiberGrouping.fiberCount P p g)
def input (F G m a c P : PTm n) : Fm PTm n := GaussianPolynomialMonicNorm.input F G m a c ⋏
  GaussianRationalCurveFibers.sourceInput F G m P

@[simp] theorem subst_sourceQuotient {l : ℕ} (σ : Fin n → PTm l) (F G m a c P p g : PTm n) :
    Syn.subst σ (sourceQuotient F G m a c P p g) = sourceQuotient (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ g) := by simp [sourceQuotient]
@[simp] theorem subst_sourceOriginal {l : ℕ} (σ : Fin n → PTm l) (F G m a c : PTm n) :
    Syn.subst σ (sourceOriginal F G m a c) = sourceOriginal (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) := by simp [sourceOriginal]
@[simp] theorem subst_sourcePadded {l : ℕ} (σ : Fin n → PTm l) (F G m a c P p g : PTm n) :
    Syn.subst σ (sourcePadded F G m a c P p g) = sourcePadded (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ g) := by simp [sourcePadded]
@[simp] theorem subst_sourceFactor {l : ℕ} (σ : Fin n → PTm l) (F G m a c P p g : PTm n) :
    Syn.subst σ (sourceFactor F G m a c P p g) = sourceFactor (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ g) := by simp [sourceFactor]
@[simp] theorem subst_sourceWidth {l : ℕ} (σ : Fin n → PTm l) (m a c P p g : PTm n) :
    Syn.subst σ (sourceWidth m a c P p g) = sourceWidth (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c)
      (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ g) := by simp [sourceWidth]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (F G m a c P : PTm n) :
    (input F G m a c P).subst σ = input (Syn.subst σ F) (Syn.subst σ G) (Syn.subst σ m)
      (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ P) := by simp [input]

theorem source_norm_identity (F G m a c : PTm n) : Γ ⊢[PRAAx]
    determinant (GaussianRationalFiberVandermonde.sourceMatrix F G m a c) m (GaussianPolynomialMonicNorm.width m a c) ≐
      sourceOriginal F G m a c :=
  (GaussianPolynomialDeterminant.partial_congr (GaussianPolynomialMonicNorm.returned_matrix _ _ _ _ _)
    (.eqRefl _) (.eqRefl _) (.eqRefl _)).eqTrans (GaussianPolynomialMonicNorm.returned_norm _ _ _ _ _).eqSymm
theorem source_padded_identity (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    paddedOriginal (GaussianRationalFiberVandermonde.sourceMatrix F G m a c) m (GaussianPolynomialMonicNorm.width m a c)
      (GaussianRationalFiberGrouping.fiberCount P p g) ≐ sourcePadded F G m a c P p g :=
  pad_congr (source_norm_identity _ _ _ _ _) (.eqRefl _)
theorem source_count_bound (F G m P p g : PTm n)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m P) : Γ ⊢[PRAAx]
    le (GaussianRationalFiberGrouping.fiberCount P p g) m :=
  le_congr (GaussianRationalCurveFibers.y_length _ _ _) (.eqRefl _)
    (GaussianRationalFiberVandermonde.source_fiber_bound _ _ _ _ _ _ hPoints)

theorem source_evaluation_factor (F G m a c P p g z : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m P) : Γ ⊢[PRAAx]
    evaluate (sourceOriginal F G m a c) z ≐
      qmul (power (qsub z (GaussianRationalCurveFibers.selectedX P p g)) (GaussianRationalFiberGrouping.fiberCount P p g))
        (evaluate (sourceQuotient F G m a c P p g) z) :=
  (GaussianRationalMonicReduction.evaluate_congr (source_norm_identity _ _ _ _ _).eqSymm (.eqRefl _)).eqTrans
    (evaluation_factor _ _ _ _ _ _ _ (GaussianRationalFiberVandermonde.source_matrix_shape _ _ _ _ _ hNorm)
      (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ (.andE₁ hPoints))
      (GaussianRationalFiberVandermonde.source_fiber_bound _ _ _ _ _ _ hPoints)
      (GaussianRationalFiberVandermonde.source_zero_rows _ _ _ _ _ _ _ _ hNorm hPoints)
      (source_count_bound _ _ _ _ _ _ hPoints))

theorem source_coefficients_factor (F G m a c P p g : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m P) : Γ ⊢[PRAAx]
    coefficientsEqual (sourcePadded F G m a c P p g) (sourceFactor F G m a c P p g) (sourceWidth m a c P p g) :=
  coefficients_left_congr (source_padded_identity _ _ _ _ _ _ _ _)
    (coefficients_factor _ _ _ _ _ _ (GaussianRationalFiberVandermonde.source_matrix_shape _ _ _ _ _ hNorm)
      (GaussianRationalCurveFibers.fiber_ordinates_distinct _ _ _ (.andE₁ hPoints))
      (GaussianRationalFiberVandermonde.source_fiber_bound _ _ _ _ _ _ hPoints)
      (GaussianRationalFiberVandermonde.source_zero_rows _ _ _ _ _ _ _ _ hNorm hPoints)
      (source_count_bound _ _ _ _ _ _ hPoints))
theorem source_coefficient_factor (F G m a c P p g i : PTm n)
    (hNorm : Γ ⊢[PRAAx] GaussianPolynomialMonicNorm.input F G m a c)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m P)
    (hi : Γ ⊢[PRAAx] le i (sourceWidth m a c P p g)) : Γ ⊢[PRAAx]
    entry (sourcePadded F G m a c P p g) i ≐ entry (sourceFactor F G m a c P p g) i :=
  coefficients_at _ _ _ _ (source_coefficients_factor _ _ _ _ _ _ _ _ hNorm hPoints) hi

theorem source_quotient_length (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    length (sourceQuotient F G m a c P p g) ≐ succ (GaussianPolynomialMonicNorm.degreeBound m a c) :=
  quotient_length _ _ _ _ _ _
theorem source_quotient_canonical (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    canonicalCoefficients (sourceQuotient F G m a c P p g) := quotient_canonical _ _ _ _ _ _
theorem source_padded_length (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    length (sourcePadded F G m a c P p g) ≐ succ (sourceWidth m a c P p g) :=
  (congrFst (source_padded_identity _ _ _ _ _ _ _ _)).eqSymm.eqTrans (padded_length _ _ _ _)
theorem source_product_length (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    length (sourceFactor F G m a c P p g) ≐ succ (sourceWidth m a c P p g) := product_length _ _ _ _ _ _
theorem source_weight_nonzero (F G m P p g : PTm n)
    (hPoints : Γ ⊢[PRAAx] GaussianRationalCurveFibers.sourceInput F G m P) : Γ ⊢[PRAAx]
    neg (scalarDet (W (GaussianRationalCurveFibers.yList P p g) m) m ≐ qzero) :=
  GaussianFiberDeterminantNonzero.source_nonzero _ _ _ _ _ (.andE₁ (.andE₂ hPoints)) (.andE₁ hPoints)

def certificate (F G m a c P p g : PTm n) : Fm PTm n :=
  (length (sourceQuotient F G m a c P p g) ≐ succ (GaussianPolynomialMonicNorm.degreeBound m a c)) ⋏
    (canonicalCoefficients (sourceQuotient F G m a c P p g) ⋏
      (le (GaussianRationalFiberGrouping.fiberCount P p g) m ⋏
        (neg (scalarDet (W (GaussianRationalCurveFibers.yList P p g) m) m ≐ qzero) ⋏
          (coefficientsEqual (sourcePadded F G m a c P p g) (sourceFactor F G m a c P p g) (sourceWidth m a c P p g) ⋏
            (GaussianRationalFiberGrouping.partitionTotal P p ≐ length P)))))
@[simp] theorem subst_certificate {l : ℕ} (σ : Fin n → PTm l) (F G m a c P p g : PTm n) :
    (certificate F G m a c P p g).subst σ = certificate (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ g) := by simp [certificate]
theorem source_factorization (F G m a c P p g : PTm n) (h : Γ ⊢[PRAAx] input F G m a c P) : Γ ⊢[PRAAx]
    certificate F G m a c P p g :=
  .andI (source_quotient_length _ _ _ _ _ _ _ _) (.andI (source_quotient_canonical _ _ _ _ _ _ _ _)
    (.andI (source_count_bound _ _ _ _ _ _ (.andE₂ h)) (.andI (source_weight_nonzero _ _ _ _ _ _ (.andE₂ h))
      (.andI (source_coefficients_factor _ _ _ _ _ _ _ _ (.andE₁ h) (.andE₂ h)) (GaussianRationalFiberGrouping.cardinal_partition _ _)))))

/-! The actual PR8 retains the old source and norm runs, the computed
quotient, the repeated-root factor and both coefficient buffers. -/
def output (F G m a c P p g : PTm n) : PTm n :=
  pairT (GaussianRationalFiberVandermonde.run F G m a c P p g)
    (pairT (GaussianPolynomialMonicNorm.run F G m a c)
      (pairT (sourceQuotient F G m a c P p g)
        (pairT (H (GaussianRationalCurveFibers.selectedX P p g) (GaussianRationalFiberGrouping.fiberCount P p g))
          (pairT (sourcePadded F G m a c P p g) (sourceFactor F G m a c P p g)))))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (F G m a c P p g : PTm n) : PTm n := app outputF ![F,G,m,a,c,P,p,g]
def fields (c : PTm n) (i : Fin 6) : PTm n :=
  ![fstT c,fstT (sndT c),fstT (sndT (sndT c)),fstT (sndT (sndT (sndT c))),
    fstT (sndT (sndT (sndT (sndT c)))),sndT (sndT (sndT (sndT (sndT c))))] i
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (F G m a c P p g : PTm n) :
    Syn.subst σ (output F G m a c P p g) = output (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ g) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (F G m a c P p g : PTm n) :
    Syn.subst σ (run F G m a c P p g) = run (Syn.subst σ F) (Syn.subst σ G)
      (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ P) (Syn.subst σ p) (Syn.subst σ g) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (c : PTm n) (i : Fin 6) :
    Syn.subst σ (fields c i) = fields (Syn.subst σ c) i := by fin_cases i <;> simp [fields]
theorem program_at (F G m a c P p g : PTm n) : Γ ⊢[PRAAx] run F G m a c P p g ≐ output F G m a c P p g := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![F,G,m,a,c,P,p,g]
theorem returned_fields (F G m a c P p g : PTm n) (i : Fin 6) : Γ ⊢[PRAAx]
    fields (run F G m a c P p g) i ≐
      ![GaussianRationalFiberVandermonde.run F G m a c P p g,GaussianPolynomialMonicNorm.run F G m a c,
        sourceQuotient F G m a c P p g,H (GaussianRationalCurveFibers.selectedX P p g) (GaussianRationalFiberGrouping.fiberCount P p g),
        sourcePadded F G m a c P p g,sourceFactor F G m a c P p g] i := by
  have e0 := program_at (Γ := Γ) F G m a c P p g
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  have e3 := (congrSnd e2).eqTrans (snd_pair _ _)
  have e4 := (congrSnd e3).eqTrans (snd_pair _ _)
  have e5 := (congrSnd e4).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrFst e3).eqTrans (fst_pair _ _)
  · exact (congrFst e4).eqTrans (fst_pair _ _)
  · exact e5

theorem returned_original (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    fstT (fields (run F G m a c P p g) 1) ≐ sourceOriginal F G m a c :=
  congrFst (returned_fields _ _ _ _ _ _ _ _ 1)
theorem returned_R (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (fields (run F G m a c P p g) 0)) ≐ GaussianRationalCurveFibers.yList P p g :=
  (congrFst (congrSnd (returned_fields _ _ _ _ _ _ _ _ 0))).eqTrans (GaussianRationalFiberVandermonde.returned_R _ _ _ _ _ _ _ _)
theorem returned_t (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (fields (run F G m a c P p g) 0))) ≐ GaussianRationalFiberGrouping.fiberCount P p g :=
  (congrFst (congrSnd (congrSnd (returned_fields _ _ _ _ _ _ _ _ 0)))).eqTrans (GaussianRationalFiberVandermonde.returned_t _ _ _ _ _ _ _ _)
theorem returned_x (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (fields (run F G m a c P p g) 0)))) ≐ GaussianRationalCurveFibers.selectedX P p g :=
  (congrFst (congrSnd (congrSnd (congrSnd (returned_fields _ _ _ _ _ _ _ _ 0))))).eqTrans (GaussianRationalFiberVandermonde.returned_x _ _ _ _ _ _ _ _)
theorem returned_partition (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (fields (run F G m a c P p g) 0)))) ≐ length P :=
  (congrSnd (congrSnd (congrSnd (congrSnd (returned_fields _ _ _ _ _ _ _ _ 0))))).eqTrans
    (GaussianRationalFiberVandermonde.returned_cardinal_partition _ _ _ _ _ _ _ _)
theorem returned_quotient_length (F G m a c P p g : PTm n) : Γ ⊢[PRAAx]
    length (fields (run F G m a c P p g) 2) ≐ succ (GaussianPolynomialMonicNorm.degreeBound m a c) :=
  (congrFst (returned_fields _ _ _ _ _ _ _ _ 2)).eqTrans (source_quotient_length _ _ _ _ _ _ _ _)
theorem returned_coefficient_factor (F G m a c P p g i : PTm n)
    (h : Γ ⊢[PRAAx] input F G m a c P) (hi : Γ ⊢[PRAAx] le i (sourceWidth m a c P p g)) : Γ ⊢[PRAAx]
    entry (fields (run F G m a c P p g) 4) i ≐ entry (fields (run F G m a c P p g) 5) i :=
  (entry_congr (returned_fields _ _ _ _ _ _ _ _ 4) (.eqRefl _)).eqTrans
    ((source_coefficient_factor _ _ _ _ _ _ _ _ _ (.andE₁ h) (.andE₂ h) hi).eqTrans
      (entry_congr (returned_fields _ _ _ _ _ _ _ _ 5) (.eqRefl _)).eqSymm)

/-! Original F/G/degree-bound data, the point list, grouping data and every
query index are internally bound. No final factor or inverse law occurs
in the source input. -/
theorem actual_source_evaluation_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      evaluate (sourceOriginal (var 0) (var 1) (var 2) (var 3) (var 4)) (var 8) ≐
        qmul (power (qsub (var 8) (GaussianRationalCurveFibers.selectedX (var 5) (var 6) (var 7)))
          (GaussianRationalFiberGrouping.fiberCount (var 5) (var 6) (var 7)))
          (evaluate (sourceQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) (var 8))) :=
  closeUniv 9 (.impI (source_evaluation_factor _ _ _ _ _ _ _ _ _ (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))
theorem actual_source_coefficient_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      le (var 8) (sourceWidth (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) ⟶
        entry (sourcePadded (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) (var 8) ≐
          entry (sourceFactor (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) (var 8)) :=
  closeUniv 9 (.impI (.impI (source_coefficient_factor _ _ _ _ _ _ _ _ _ (.andE₁ Prf.hyp1) (.andE₂ Prf.hyp1) Prf.hyp0)))
theorem actual_source_divisibility_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (.impI (source_factorization _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_source_quotient_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((length (sourceQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) ≐
      succ (GaussianPolynomialMonicNorm.degreeBound (var 2) (var 3) (var 4))) ⋏
        canonicalCoefficients (sourceQuotient (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.andI (source_quotient_length _ _ _ _ _ _ _ _) (source_quotient_canonical _ _ _ _ _ _ _ _))
theorem actual_common_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((length (sourcePadded (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) ≐
      succ (sourceWidth (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) ⋏
        (length (sourceFactor (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) ≐
          succ (sourceWidth (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))) :=
  closeUniv 8 (.andI (source_padded_length _ _ _ _ _ _ _ _) (source_product_length _ _ _ _ _ _ _ _))
theorem actual_source_weight_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      neg (scalarDet (W (GaussianRationalCurveFibers.yList (var 5) (var 6) (var 7)) (var 2)) (var 2) ≐ qzero)) :=
  closeUniv 8 (.impI (source_weight_nonzero _ _ _ _ _ _ (.andE₂ Prf.hyp0)))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at _ _ _ _ _ _ _ _)
theorem actual_original_norm_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (fstT (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 1) ≐
      sourceOriginal (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 8 (returned_original _ _ _ _ _ _ _ _)
theorem actual_returned_coefficient_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      le (var 8) (sourceWidth (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) ⟶
        entry (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 4) (var 8) ≐
          entry (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 5) (var 8)) :=
  closeUniv 9 (.impI (.impI (returned_coefficient_factor _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_source_data_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((fstT (sndT (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 0)) ≐
      GaussianRationalCurveFibers.yList (var 5) (var 6) (var 7)) ⋏
        ((fstT (sndT (sndT (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 0))) ≐
          GaussianRationalFiberGrouping.fiberCount (var 5) (var 6) (var 7)) ⋏
            ((fstT (sndT (sndT (sndT (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 0)))) ≐
              GaussianRationalCurveFibers.selectedX (var 5) (var 6) (var 7)) ⋏
                (sndT (sndT (sndT (sndT (fields (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) 0)))) ≐ length (var 5))))) :=
  closeUniv 8 (.andI (returned_R _ _ _ _ _ _ _ _) (.andI (returned_t _ _ _ _ _ _ _ _)
    (.andI (returned_x _ _ _ _ _ _ _ _) (returned_partition _ _ _ _ _ _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianNormFiberDivisibility
