import Surreal.Algebra.DecomposableFibers
import Mathlib.RingTheory.Norm.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# The cubic norm form for a cube root of two

The displayed example following `odg:thm:norm`. We compute the multiplication
matrix determinant, diagonalize it at the three distinct complex cube roots
of two, and deduce constant-coordinate rigidity from the constant-unit property.
-/

namespace Surreal.CubicNorm

noncomputable section

/-- The cubic form displayed in the norm-rigidity example. -/
def value {R : Type*} [CommRing R] (x y z : R) : R :=
  x ^ 3 + 2 * y ^ 3 + 4 * z ^ 3 - 6 * x * y * z

@[simp] theorem map_value {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (x y z : R) : φ (value x y z) = value (φ x) (φ y) (φ z) := by
  simp only [value, map_sub, map_add, map_mul, map_pow, map_ofNat]

/-- Multiplication by x + y θ + z θ² in the power basis, with θ³ = 2. -/
def multiplicationMatrix {R : Type*} [CommRing R] (x y z : R) : Matrix (Fin 3) (Fin 3) R :=
  !![x, 2 * z, 2 * y; y, x, 2 * z; z, y, x]

/-- Exact determinant calculation over every commutative ring. -/
theorem det_multiplicationMatrix {R : Type*} [CommRing R] (x y z : R) :
    (multiplicationMatrix x y z).det = value x y z := by
  simp [multiplicationMatrix, Matrix.det_fin_three, value]
  ring

/-- The displayed matrix is the native multiplication matrix whenever the basis is
1, θ, θ² and θ³ = 2. -/
theorem leftMulMatrix {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (b : Module.Basis (Fin 3) R S) (θ : S) (hb : ∀ i, b i = θ ^ (i : ℕ))
    (hθ : θ ^ 3 = 2) (x y z : R) :
    Algebra.leftMulMatrix b (algebraMap R S x + algebraMap R S y * θ +
      algebraMap R S z * θ ^ 2) = multiplicationMatrix x y z := by
  have hcol (j : Fin 3) :
      (algebraMap R S x + algebraMap R S y * θ + algebraMap R S z * θ ^ 2) * b j =
        ∑ i, multiplicationMatrix x y z i j • b i := by
    fin_cases j <;>
      simp [hb, Fin.sum_univ_succ, multiplicationMatrix, Algebra.smul_def, map_ofNat]
    · ring
    · linear_combination algebraMap R S z * hθ
    · linear_combination (algebraMap R S y + algebraMap R S z * θ) * hθ
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, hcol]
  simp [map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply]

/-- The polynomial is Mathlib's algebra norm in every such power basis. -/
theorem algebra_norm {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (b : Module.Basis (Fin 3) R S) (θ : S) (hb : ∀ i, b i = θ ^ (i : ℕ))
    (hθ : θ ^ 3 = 2) (x y z : R) :
    Algebra.norm R (algebraMap R S x + algebraMap R S y * θ + algebraMap R S z * θ ^ 2) =
      value x y z := by
  rw [Algebra.norm_eq_matrix_det b, leftMulMatrix b θ hb hθ, det_multiplicationMatrix]

/-- Evaluation at cube roots diagonalizes the multiplication matrix. -/
theorem diagonalization {R : Type*} [CommRing R] (r : Fin 3 → R)
    (hr : ∀ i, r i ^ 3 = 2) (x y z : R) :
    Matrix.vandermonde r * multiplicationMatrix x y z =
      Matrix.diagonal (fun i => x + r i * y + r i ^ 2 * z) * Matrix.vandermonde r := by
  ext i j
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vandermonde_apply,
      multiplicationMatrix, Matrix.diagonal]
  · ring
  · linear_combination -z * (hr i)
  · linear_combination -(y + z * r i) * (hr i)

/-- The determinant is the product of the three conjugate linear forms. -/
theorem factorization {R : Type*} [CommRing R] (r : Fin 3 → R)
    (hr : ∀ i, r i ^ 3 = 2) (hu : IsUnit (Matrix.vandermonde r).det) (x y z : R) :
    value x y z = ∏ i, (x + r i * y + r i ^ 2 * z) := by
  have h := congrArg Matrix.det (diagonalization r hr x y z)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_multiplicationMatrix,
    mul_comm _ (Matrix.vandermonde r).det] at h
  exact hu.mul_left_cancel h

/-- Three distinct complex cube roots of two, obtained from a primitive cube root of unity. -/
theorem exists_complex_roots :
    ∃ r : Fin 3 → ℂ, Function.Injective r ∧ ∀ i, r i ^ 3 = 2 := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℂ) (by decide : 0 < 3)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ 3
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  refine ⟨fun i => a * ζ ^ (i : ℕ), ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    exact hζ.pow_inj i.isLt j.isLt (mul_left_cancel₀ ha0 h)
  · intro i
    rw [mul_pow, ha, ← pow_mul, Nat.mul_comm (i : ℕ) 3, pow_mul, hζ.pow_eq_one]
    simp

/-- At a nonzero constant level, the cubic has constant coordinates in any complex algebra
whose units are constants. -/
theorem coordinates_constant {B : Type*} [CommRing B] [Algebra ℂ B]
    (ct : B →ₐ[ℂ] ℂ) (hunit : ∀ z : B, IsUnit z → z = algebraMap ℂ B (ct z))
    (c : ℂ) (hc : c ≠ 0) (x : Fin 3 → B)
    (hx : value (x 0) (x 1) (x 2) = algebraMap ℂ B c) :
    ∀ j, x j = algebraMap ℂ B (ct (x j)) := by
  obtain ⟨r, hi, hr⟩ := exists_complex_roots
  have hu : IsUnit (Matrix.vandermonde r).det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hi)
  have hm : Matrix.vandermonde (fun i => algebraMap ℂ B (r i)) =
      (algebraMap ℂ B).mapMatrix (Matrix.vandermonde r) := by
    ext i j
    simp [Matrix.vandermonde_apply]
  have hp := factorization (fun i => algebraMap ℂ B (r i))
    (fun i => by rw [← map_pow, hr i, map_ofNat])
    (by rw [hm, ← RingHom.map_det]; exact hu.map (algebraMap ℂ B)) (x 0) (x 1) (x 2)
  apply DecomposableFibers.coordinates_constant_of_injective ct hunit
    (fun _ => 0) (Matrix.vandermonde r) (fun _ => 1) (fun _ => one_ne_zero) c hc x
  · rw [← hx, hp]
    simp [DecomposableFibers.value, DecomposableFibers.affineValue,
      Fin.sum_univ_succ, Matrix.vandermonde_apply, Algebra.smul_def, map_pow, add_assoc]
  · exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hu)

end
end Surreal.CubicNorm
