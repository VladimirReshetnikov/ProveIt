import Surreal.Algebra.DecomposableFibers
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Tactic.LinearCombination

/-!
# Rigidity from two distinct projective linear factors

Generic polynomial algebra for `odg:thm:binary`. Two independent homogeneous
linear divisors suffice for rigidity of a nonzero constant level in any
split constant-field algebra whose units are constants. The polynomial
itself need not be homogeneous.
-/

namespace Surreal.BinaryFormRigidity

open MvPolynomial

noncomputable section

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]

/-- A native homogeneous linear polynomial in two variables. -/
def linearForm (a b : K) : MvPolynomial (Fin 2) K := C a * X 0 + C b * X 1

/-- Two projectively distinct linear factors, expressed by polynomial divisibility and determinant. -/
def HasTwoProjectiveFactors (p : MvPolynomial (Fin 2) K) : Prop :=
  ∃ a b c d : K, a * d - b * c ≠ 0 ∧ linearForm a b ∣ p ∧ linearForm c d ∣ p

/-- For a nonzero first coefficient vector, determinant zero is exactly proportionality. -/
theorem determinant_zero_iff_proportional (a b c d : K) (hab : a ≠ 0 ∨ b ≠ 0) :
    a * d - b * c = 0 ↔ ∃ r : K, c = r * a ∧ d = r * b := by
  constructor
  · intro h
    rcases hab with ha | hb
    · refine ⟨c / a, ?_, ?_⟩
      · field_simp
      · apply (mul_left_cancel₀ ha)
        field_simp
        linear_combination h
    · refine ⟨d / b, ?_, ?_⟩
      · apply (mul_left_cancel₀ hb)
        field_simp
        linear_combination -h
      · field_simp
  · rintro ⟨r, rfl, rfl⟩
    ring

/-- The determinant formulation is exactly two nonproportional nonzero projective factors. -/
theorem hasTwoProjectiveFactors_iff (p : MvPolynomial (Fin 2) K) :
    HasTwoProjectiveFactors p ↔ ∃ a b c d : K,
      (a ≠ 0 ∨ b ≠ 0) ∧ (¬ ∃ r : K, c = r * a ∧ d = r * b) ∧
      linearForm a b ∣ p ∧ linearForm c d ∣ p := by
  constructor
  · rintro ⟨a, b, c, d, hd, h₁, h₂⟩
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨rfl, rfl⟩ := h
      simp at hd
    exact ⟨a, b, c, d, hab, fun h => hd ((determinant_zero_iff_proportional a b c d hab).mpr h),
      h₁, h₂⟩
  · rintro ⟨a, b, c, d, hab, hd, h₁, h₂⟩
    exact ⟨a, b, c, d, fun h => hd ((determinant_zero_iff_proportional a b c d hab).mp h), h₁, h₂⟩

/-- Evaluating a linear divisor at a nonzero constant level kills its nonconstant linear part. -/
theorem linear_factor_residual (ct : B →ₐ[K] K)
    (hunit : ∀ z : B, IsUnit z → z = algebraMap K B (ct z))
    (p : MvPolynomial (Fin 2) K) (a b : K) (hab : linearForm a b ∣ p)
    (x : Fin 2 → B) (c : K) (hc : c ≠ 0)
    (hx : p.eval₂ (algebraMap K B) x = algebraMap K B c) :
    algebraMap K B a * (x 0 - algebraMap K B (ct (x 0))) +
      algebraMap K B b * (x 1 - algebraMap K B (ct (x 1))) = 0 := by
  have hu : IsUnit (p.eval₂ (algebraMap K B) x) := hx ▸
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap K B)
  have hf := hunit _ (isUnit_of_dvd_unit
    (map_dvd (MvPolynomial.eval₂Hom (algebraMap K B) x) hab) hu)
  simp only [linearForm, MvPolynomial.coe_eval₂Hom, eval₂_C, eval₂_X,
    map_add, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply] at hf
  linear_combination hf

/-- A nonzero constant level of any polynomial with two projectively distinct linear divisors
has only constant coordinates. This includes homogeneous binary forms. -/
theorem coordinates_constant (ct : B →ₐ[K] K)
    (hunit : ∀ z : B, IsUnit z → z = algebraMap K B (ct z))
    (p : MvPolynomial (Fin 2) K) (hp : HasTwoProjectiveFactors p)
    (x : Fin 2 → B) (c : K) (hc : c ≠ 0)
    (hx : p.eval₂ (algebraMap K B) x = algebraMap K B c) :
    ∀ k, x k = algebraMap K B (ct (x k)) := by
  obtain ⟨a, b, d, e, hdet, h₁, h₂⟩ := hp
  have h₁ := linear_factor_residual ct hunit p a b h₁ x c hc hx
  have h₂ := linear_factor_residual ct hunit p d e h₂ x c hc hx
  have hu : IsUnit (algebraMap K B (a * e - b * d)) :=
    (isUnit_iff_ne_zero.mpr hdet).map (algebraMap K B)
  have hzero (k : Fin 2) : x k - algebraMap K B (ct (x k)) = 0 := by
    apply hu.mul_left_cancel
    rw [mul_zero, map_sub, map_mul, map_mul]
    fin_cases k
    · change (algebraMap K B a * algebraMap K B e - algebraMap K B b * algebraMap K B d) *
        (x 0 - algebraMap K B (ct (x 0))) = 0
      linear_combination algebraMap K B e * h₁ - algebraMap K B b * h₂
    · change (algebraMap K B a * algebraMap K B e - algebraMap K B b * algebraMap K B d) *
        (x 1 - algebraMap K B (ct (x 1))) = 0
      linear_combination algebraMap K B a * h₂ - algebraMap K B d * h₁
  exact fun k => sub_eq_zero.mp (hzero k)

end
end Surreal.BinaryFormRigidity
