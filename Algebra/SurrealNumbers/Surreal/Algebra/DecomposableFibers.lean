import Surreal.Algebra.ModuleKernelBasis
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Commute.Units

/-!
# Fibers of products of affine forms over a split constant field

Algebraic prerequisites for `odg:lem:constantproduct` and `odg:thm:decomposable`.
The ambient ring retracts onto a field and its units are constants. A nonzero
constant product forces every factor to be constant, and hence forces the
nonconstant part of a tuple into the common kernel of the linear forms.
-/

namespace Surreal.DecomposableFibers

open Matrix

variable {K B m n : Type*} [Field K] [CommRing B] [Algebra K B]
variable [Fintype m] [Fintype n]

/-- Evaluate the affine factors with coefficients in the constant field. -/
def affineValue (β : m → K) (A : Matrix m n K) (x : n → B) (j : m) : B :=
  algebraMap K B (β j) + ∑ k, A j k • x k

/-- Evaluate the product of positive powers of the affine factors. -/
def value (β : m → K) (A : Matrix m n K) (e : m → ℕ) (x : n → B) : B :=
  ∏ j, affineValue β A x j ^ e j

/-- Subtract the constant part coordinatewise. -/
def residual (ct : B →ₐ[K] K) (x : n → B) (k : n) : B :=
  x k - algebraMap K B (ct (x k))

omit [Fintype m] in
/-- The retraction evaluates affine factors in the constant field. -/
theorem map_affineValue (ct : B →ₐ[K] K) (β : m → K) (A : Matrix m n K)
    (x : n → B) (j : m) :
    ct (affineValue β A x j) = affineValue β A (fun k => ct (x k)) j := by
  simp [affineValue]

/-- The retraction evaluates the whole product in the constant field. -/
theorem map_value (ct : B →ₐ[K] K) (β : m → K) (A : Matrix m n K)
    (e : m → ℕ) (x : n → B) :
    ct (value β A e x) = value β A e (fun k => ct (x k)) := by
  simp [value, map_affineValue]

omit [Fintype m] in
/-- The linear value of the residual is the nonconstant part of the affine factor. -/
theorem linear_residual (ct : B →ₐ[K] K) (β : m → K) (A : Matrix m n K)
    (x : n → B) (j : m) :
    ∑ k, A j k • residual ct x k =
      affineValue β A x j - algebraMap K B (ct (affineValue β A x j)) := by
  simp [residual, affineValue, mul_sub, Finset.sum_sub_distrib, Algebra.smul_def]

/-- Every factor of a nonzero constant product is a nonzero constant. -/
theorem factors_constant (ct : B →ₐ[K] K)
    (hunit : ∀ z : B, IsUnit z → z = algebraMap K B (ct z))
    (f : m → B) (c : K) (hc : c ≠ 0) (h : ∏ j, f j = algebraMap K B c) :
    ∀ j, ct (f j) ≠ 0 ∧ f j = algebraMap K B (ct (f j)) := by
  have hu : IsUnit (∏ j, f j) := h ▸ (isUnit_iff_ne_zero.mpr hc).map (algebraMap K B)
  intro j
  have hj := IsUnit.prod_univ_iff.mp hu j
  exact ⟨(hj.map ct.toRingHom).ne_zero, hunit _ hj⟩

/-- Nonzero constant fibers are exactly constant solutions plus common-kernel residuals. -/
theorem value_eq_iff (ct : B →ₐ[K] K)
    (hunit : ∀ z : B, IsUnit z → z = algebraMap K B (ct z))
    (β : m → K) (A : Matrix m n K) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : K) (hc : c ≠ 0) (x : n → B) :
    value β A e x = algebraMap K B c ↔
      value β A e (fun k => ct (x k)) = c ∧
      ∀ j, ∑ k, A j k • residual ct x k = 0 := by
  constructor
  · intro hx
    have hu : IsUnit (value β A e x) := hx ▸
      (isUnit_iff_ne_zero.mpr hc).map (algebraMap K B)
    refine ⟨?_, fun j => ?_⟩
    · simpa only [map_value, AlgHom.commutes, Algebra.algebraMap_self_apply] using congrArg ct hx
    · have hj := (isUnit_pow_iff (he j)).mp (IsUnit.prod_univ_iff.mp hu j)
      rw [linear_residual]
      exact sub_eq_zero.mpr (hunit _ hj)
  · rintro ⟨hx, hk⟩
    have hf (j : m) : affineValue β A x j =
        algebraMap K B (affineValue β A (fun k => ct (x k)) j) := by
      have h := hk j
      rw [linear_residual, sub_eq_zero, map_affineValue] at h
      exact h
    simp only [value, hf, ← map_pow, ← map_prod]
    exact congrArg (algebraMap K B) hx

variable [DecidableEq m] [DecidableEq n]

/-- Independent columns force every coordinate in a nonzero constant fiber to be constant. -/
theorem coordinates_constant_of_injective (ct : B →ₐ[K] K)
    (hunit : ∀ z : B, IsUnit z → z = algebraMap K B (ct z))
    (β : m → K) (A : Matrix m n K) (e : m → ℕ) (he : ∀ j, e j ≠ 0)
    (c : K) (hc : c ≠ 0) (x : n → B)
    (hx : value β A e x = algebraMap K B c) (hA : Function.Injective A.mulVecLin) :
    ∀ k, x k = algebraMap K B (ct (x k)) := by
  have hk := ((value_eq_iff ct hunit β A e he c hc x).mp hx).2
  have hz := ModuleKernelBasis.eq_zero_of_injective A hA (residual ct x) hk
  intro k
  have h := congrFun hz k
  exact sub_eq_zero.mp h

end Surreal.DecomposableFibers
