import IPRADerivations.Analysis.GaussianScalarPolynomialMatrixProduct
import IPRADerivations.Analysis.GaussianScalarDeterminantMultiplication
import IPRADerivations.Analysis.GaussianRationalGridCoefficientEquality

/-!
# The determinant of the actual scalar-left polynomial matrix product

The scalar matrix is applied to each stored polynomial cell using the
original matrix product. At each query, these cells evaluate to the
corresponding scalar matrix product. The actual scalar determinant law
therefore applies at every numerical query, including every finite grid
point used for coefficient comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialScalarLeftDeterminant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate qmul)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (tableShape)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminant (determinant)
open LeanProofs.IPRA.Analysis.GaussianScalarDeterminant (scalarDet evaluatedTable)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Multiplication by the original scalar matrix commutes with determinant
evaluation, under the original polynomial cell shape. -/
theorem product_evaluation (S M m L z : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) :
    Γ ⊢[PRAAx]
      evaluate (determinant (GaussianRationalFiberVandermonde.product S M m L) m L) z ≐
        qmul (scalarDet S m) (evaluate (determinant M m L) z) := by
  have evaluated := GaussianScalarPolynomialMatrixProduct.determinant_evaluation_bridge S M m L z hM
  have multiplied := GaussianScalarDeterminantMultiplication.scalar_det_multiply (Γ := Γ)
    S (evaluatedTable M m z) m
  have right := GaussianScalarDeterminant.determinant_evaluation_specialization M m L z hM
  exact evaluated.eqTrans (multiplied.eqTrans (qmul_congr (.eqRefl _) right.eqSymm))

theorem WM_evaluation (R M m L z : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) :
    Γ ⊢[PRAAx]
      evaluate (determinant (GaussianRationalFiberVandermonde.WM R M m L) m L) z ≐
        qmul (scalarDet (GaussianRationalFiberVandermonde.W R m) m)
          (evaluate (determinant M m L) z) :=
  product_evaluation _ _ _ _ _ hM

theorem product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 1) (var 2) (var 3) ⟶
      evaluate (determinant (GaussianRationalFiberVandermonde.product (var 0) (var 1) (var 2) (var 3))
        (var 2) (var 3)) (var 4) ≐
      qmul (scalarDet (var 0) (var 2)) (evaluate (determinant (var 1) (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (product_evaluation _ _ _ _ _ Prf.hyp0))

open GaussianRationalCoefficientScaling (scaled scaled_length scaled_entry_canonical subst_scaled evaluation_linearity)
open GaussianRationalSyntheticDivision (canonicalCoefficients)
open GaussianRationalGridCoefficientEquality (gridEqual coefficientsEqual coefficients_equal)
open GaussianRationalFiniteGridIdentity (gridPoint)
open GaussianRationalFiberVandermonde (product WM W subst_product)
open GaussianPolynomialDeterminant (determinant_length determinant_canonical subst_determinant)
open GaussianScalarDeterminant (subst_scalarDet)

/-- Independently stored scalar multiple of the original determinant. -/
def scaledDeterminant (S M m L : PTm n) : PTm n := scaled (determinant M m L) (scalarDet S m)

@[simp] theorem subst_scaledDeterminant {k : ℕ} (σ : Fin n → PTm k) (S M m L : PTm n) :
    Syn.subst σ (scaledDeterminant S M m L) =
      scaledDeterminant (Syn.subst σ S) (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) := by
  simp [scaledDeterminant]

theorem scaled_canonical (C s : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (scaled C s) := by
  refine .allI (.impI ?_)
  let C' := Syn.shift C
  let s' := Syn.shift s
  let i : PTm (n + 1) := var 0
  let Δ := lt i (Foundations.SequenceComposition.length (scaled C' s')) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i (Foundations.SequenceComposition.length (scaled C' s')) := Prf.hyp0
  have hbound := lt_congr (Prf.eqRefl (Γ := Δ) i) (scaled_length C' s') hi
  have result := scaled_entry_canonical (Γ := Δ) C' s' i hbound
  simpa only [Δ,i,C',s',Syn.shift,subst_scaled] using result

theorem grid_evaluation_equal (S M m L : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) :
    Γ ⊢[PRAAx] gridEqual (determinant (product S M m L) m L) (scaledDeterminant S M m L) (m * L) := by
  refine .allI (.impI ?_)
  let S' := Syn.shift S
  let M' := Syn.shift M
  let m' := Syn.shift m
  let L' := Syn.shift L
  let i : PTm (n + 1) := var 0
  let Δ := le i (m' * L') :: Γ.map Fm.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] tableShape M' m' L' := by
    simpa only [Fm.shift,M',m',L',GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using hM.shift
  have left := product_evaluation (Γ := Δ) S' M' m' L' (gridPoint i) hm.wk
  have right := evaluation_linearity (Γ := Δ) (determinant M' m' L') (scalarDet S' m') (gridPoint i)
  have result := left.eqTrans right.eqSymm
  simpa only [Δ,i,S',M',m',L',Syn.shift,subst_determinant,subst_product,
    scaledDeterminant,subst_scaled,subst_scalarDet,PTm.subst_mul] using result

/-- The two actual determinant buffers agree entrywise at all numerical indices
within their common width. -/
theorem product_coefficients (S M m L : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) :
    Γ ⊢[PRAAx] coefficientsEqual
      (determinant (product S M m L) m L) (scaledDeterminant S M m L) (m * L) :=
  coefficients_equal _ _ _
    (determinant_length _ _ _)
    ((scaled_length (determinant M m L) (scalarDet S m)).eqTrans (determinant_length _ _ _))
    (determinant_canonical _ _ _)
    (scaled_canonical _ _)
    (grid_evaluation_equal _ _ _ _ hM)

theorem WM_coefficients (R M m L : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) :
    Γ ⊢[PRAAx] coefficientsEqual
      (determinant (WM R M m L) m L) (scaledDeterminant (W R m) M m L) (m * L) :=
  product_coefficients _ _ _ _ hM

theorem product_coefficients_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (tableShape (var 1) (var 2) (var 3) ⟶ coefficientsEqual
      (determinant (product (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3))
      (scaledDeterminant (var 0) (var 1) (var 2) (var 3)) ((var 2) * (var 3))) :=
  closeUniv 4 (.impI (product_coefficients _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPolynomialScalarLeftDeterminant
