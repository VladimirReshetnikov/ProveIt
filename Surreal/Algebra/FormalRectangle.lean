import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-!
# Rectangular truncations of two-variable formal series

For the local multiplicities in `trigonometry:sec:coupled`, the quotient
by `(X^m,Y^n)` has exactly the coefficients in the `m` by `n` rectangle.
The ideal-membership criterion and coefficient equivalence are proved over
an arbitrary commutative ring; dimension is then computed over a field.
-/

namespace Surreal.FormalRectangle

open MvPowerSeries Module

noncomputable section

open Classical

variable {R : Type*} [CommRing R]

abbrev Series := MvPowerSeries (Fin 2) R

/-- The two pure powers defining the rectangular truncation. -/
def ideal (m n : ℕ) : Ideal (Series (R := R)) :=
  Ideal.span {X 0 ^ m, X 1 ^ n}

/-- Membership in the full ideal is equivalent to vanishing throughout the retained rectangle. -/
theorem mem_ideal_iff (m n : ℕ) (f : Series (R := R)) :
    f ∈ ideal m n ↔ ∀ d : Fin 2 →₀ ℕ, d 0 < m → d 1 < n → coeff d f = 0 := by
  constructor
  · intro hf d h0 h1
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hf
    rw [map_add]
    have ha : X 0 ^ m ∣ a * X 0 ^ m := dvd_mul_left _ _
    have hb : X 1 ^ n ∣ b * X 1 ^ n := dvd_mul_left _ _
    rw [X_pow_dvd_iff.mp ha d h0, X_pow_dvd_iff.mp hb d h1, add_zero]
  · intro hf
    let g : Series (R := R) := fun d => if d 0 < m then 0 else coeff d f
    have hg : X 0 ^ m ∣ g := X_pow_dvd_iff.mpr (by
      intro d hd
      simp [g, coeff_apply, hd])
    have hfg : X 1 ^ n ∣ f - g := X_pow_dvd_iff.mpr (by
      intro d hd
      rw [map_sub]
      change coeff d f - (if d 0 < m then 0 else coeff d f) = 0
      by_cases h0 : d 0 < m
      · simp [h0, hf d h0 hd]
      · simp [h0])
    have hgmem : g ∈ ideal m n :=
      Ideal.subset_span (by simp : X 0 ^ m ∈ ({X 0 ^ m, X 1 ^ n} : Set (Series (R := R))))
        |> fun hx => (ideal m n).mem_of_dvd hg hx
    have hfgmem : f - g ∈ ideal m n :=
      (ideal m n).mem_of_dvd hfg (Ideal.subset_span (by simp))
    simpa using (ideal m n).add_mem hfgmem hgmem

/-- The exponent of a retained coefficient. -/
def exponent (m n : ℕ) (ij : Fin m × Fin n) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val

@[simp] theorem exponent_zero (m n : ℕ) (ij : Fin m × Fin n) : exponent m n ij 0 = ij.1 := by
  simp [exponent]

@[simp] theorem exponent_one (m n : ℕ) (ij : Fin m × Fin n) : exponent m n ij 1 = ij.2 := by
  simp [exponent]

theorem exponent_coordinates (d : Fin 2 →₀ ℕ) :
    Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) = d := by
  ext i
  fin_cases i <;> simp

theorem exponent_injective (m n : ℕ) : Function.Injective (exponent m n) := by
  intro i j h
  apply Prod.ext
  · apply Fin.ext
    simpa using congrArg (fun d => d 0) h
  · apply Fin.ext
    simpa using congrArg (fun d => d 1) h

/-- Extract exactly the finitely many coefficients that survive in the quotient. -/
def coefficients (m n : ℕ) : Series (R := R) →ₗ[R] (Fin m × Fin n → R) :=
  LinearMap.pi (fun ij => coeff (exponent m n ij))

@[simp] theorem coefficients_apply (m n : ℕ) (f : Series (R := R)) (ij : Fin m × Fin n) :
    coefficients m n f ij = coeff (exponent m n ij) f := rfl

/-- Every prescribed rectangle is realized by a formal series, even when one side is empty. -/
theorem coefficients_surjective (m n : ℕ) :
    Function.Surjective (coefficients (R := R) m n) := by
  intro v
  refine ⟨(fun d => if h : d 0 < m ∧ d 1 < n then v (⟨d 0, h.1⟩, ⟨d 1, h.2⟩) else 0), ?_⟩
  ext ij
  simp [coefficients_apply, coeff_apply, ij.1.isLt, ij.2.isLt]

/-- The kernel is exactly the defining ideal, regarded as a coefficient-ring submodule. -/
theorem ker_coefficients (m n : ℕ) :
    LinearMap.ker (coefficients (R := R) m n) = (ideal m n).restrictScalars R := by
  ext f
  rw [LinearMap.mem_ker]
  change coefficients m n f = 0 ↔ f ∈ ideal m n
  rw [mem_ideal_iff]
  constructor
  · intro hf d h0 h1
    have hh := congrFun hf (⟨d 0, h0⟩, ⟨d 1, h1⟩)
    simpa [coefficients_apply, exponent, exponent_coordinates] using hh
  · intro hf
    ext ij
    exact hf _ (by simp) (by simp)

/-- The formal quotient is precisely the finite module of retained coefficients. -/
def quotientCoefficients (m n : ℕ) :
    (Series (R := R) ⧸ ideal (R := R) m n) ≃ₗ[R] (Fin m × Fin n → R) :=
  (Submodule.Quotient.restrictScalarsEquiv R (ideal (R := R) m n)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_coefficients (R := R) m n).symm).trans
      ((coefficients (R := R) m n).quotKerEquivOfSurjective
        (coefficients_surjective (R := R) m n)))

/-- On a series class, the equivalence returns its literal coefficients. -/
@[simp] theorem quotientCoefficients_mk (m n : ℕ) (f : Series (R := R)) :
    quotientCoefficients (R := R) m n
      (Ideal.Quotient.mk (ideal (R := R) m n) f) = coefficients (R := R) m n f := rfl

/-- The monomial coordinates give a basis of the quotient over the coefficient ring. -/
def quotientBasis (m n : ℕ) :
    Basis (Fin m × Fin n) R (Series (R := R) ⧸ ideal (R := R) m n) :=
  (Pi.basisFun R (Fin m × Fin n)).map (quotientCoefficients (R := R) m n).symm

/-- Each basis vector is exactly the corresponding monomial class. -/
theorem quotientBasis_apply (m n : ℕ) (ij : Fin m × Fin n) :
    quotientBasis (R := R) m n ij =
      Ideal.Quotient.mk (ideal (R := R) m n) (monomial (exponent m n ij) 1) := by
  apply (quotientCoefficients (R := R) m n).injective
  rw [quotientBasis, Basis.map_apply, LinearEquiv.apply_symm_apply, quotientCoefficients_mk]
  ext kl
  simp [Pi.basisFun_apply, coefficients_apply, coeff_monomial,
    (exponent_injective m n).eq_iff, Pi.single_apply, eq_comm]

/-- In particular the formal quotient is finite, not just a space with a formal finrank expression. -/
theorem quotient_finite (m n : ℕ) : Module.Finite R (Series (R := R) ⧸ ideal (R := R) m n) :=
  Module.Finite.equiv (quotientCoefficients (R := R) m n).symm

/-- Over a field the native dimension of the entire truncated formal quotient is `m*n`. -/
theorem quotient_finrank {K : Type*} [Field K] (m n : ℕ) :
    Module.finrank K (Series (R := K) ⧸ ideal (R := K) m n) = m * n := by
  rw [(quotientCoefficients (R := K) m n).finrank_eq]
  simp

end
end Surreal.FormalRectangle
