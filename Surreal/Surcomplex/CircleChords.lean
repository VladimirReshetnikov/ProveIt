import Surreal.Surcomplex.FiniteTrigonometryIdentities

/-!
# Actual circles and exact chord factorizations

Every point at a positive surreal distance from a center is reached by
a finite actual angle. The difference of two parameter points has the
exact phase and length stated in `trigonometry:eq:chordfactor`, including
infinite radii and infinitesimal angular separations. This also formalizes
the circle-parameterization assertion immediately preceding that equation.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

/-- A point on the circle with actual center, surreal radius, and finite actual angle. -/
def circlePoint (O : Surcomplex.{u}) (R : SignSequence.{u})
    (θ : SignSequence.FiniteElement.{u}) : Surcomplex.{u} :=
  O + ofReal R * finitePhase θ

/-- Every parameter point has the prescribed nonnegative actual radius. -/
theorem modulus_circlePoint_sub_center (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 ≤ R) (θ : SignSequence.FiniteElement.{u}) :
    modulus (circlePoint O R θ - O) = R := by
  rw [circlePoint, add_sub_cancel_left, modulus_mul, modulus_ofReal,
    modulus_finitePhase, mul_one, abs_of_nonneg hR]

/-- Finite actual angles parameterize every point of every positive-radius actual circle. -/
theorem mem_circle_iff_exists_circlePoint (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 < R) (z : Surcomplex.{u}) :
    modulus (z - O) = R ↔ ∃ θ : SignSequence.FiniteElement.{u}, z = circlePoint O R θ := by
  constructor
  · intro hz
    have hm : modulus (z - O) ≠ 0 := by rw [hz]; exact hR.ne'
    obtain ⟨θ, hθ⟩ := exists_polar (z - O) ((modulus_eq_zero_iff _).not.mp hm)
    rw [hz] at hθ
    refine ⟨θ, ?_⟩
    simpa only [circlePoint, add_comm] using sub_eq_iff_eq_add.mp hθ
  · rintro ⟨θ, rfl⟩
    exact modulus_circlePoint_sub_center O R hR.le θ

/-- Difference-to-product for actual phases, retaining the half-sum phase and signed half-sine. -/
theorem finitePhase_sub_factor (θ₂ θ₁ : SignSequence.FiniteElement.{u}) :
    finitePhase θ₂ - finitePhase θ₁ =
      ofReal (2 * finiteSin (finiteHalf (θ₂ - θ₁))) * I *
        finitePhase (finiteHalf (θ₁ + θ₂)) := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_sub, mul_re, mul_im, ofReal_re, ofReal_im,
      I_re, I_im, zero_mul, mul_zero, add_zero, sub_zero, zero_sub, mul_one]
    change finiteCos θ₂ - finiteCos θ₁ =
      -(2 * finiteSin (finiteHalf (θ₂ - θ₁)) * finiteSin (finiteHalf (θ₁ + θ₂)))
    rw [finiteCos_sub_finiteCos, add_comm θ₂ θ₁]
    ring
  · simp only [QuadraticAlgebra.im_sub, mul_re, mul_im, ofReal_re, ofReal_im,
      I_re, I_im, zero_mul, mul_zero, zero_add, add_zero, sub_zero, mul_one]
    change finiteSin θ₂ - finiteSin θ₁ =
      2 * finiteSin (finiteHalf (θ₂ - θ₁)) * finiteCos (finiteHalf (θ₁ + θ₂))
    rw [finiteSin_sub_finiteSin, add_comm θ₂ θ₁]
    ring

/-- The full signed circle-chord factorization, with no size restriction on the radius. -/
theorem circlePoint_sub_factor (O : Surcomplex.{u}) (R : SignSequence.{u})
    (θ₂ θ₁ : SignSequence.FiniteElement.{u}) :
    circlePoint O R θ₂ - circlePoint O R θ₁ =
      ofReal (2 * R * finiteSin (finiteHalf (θ₂ - θ₁))) * I *
        finitePhase (finiteHalf (θ₁ + θ₂)) := by
  calc
    _ = ofReal R * (finitePhase θ₂ - finitePhase θ₁) := by dsimp [circlePoint]; ring
    _ = _ := by
      rw [finitePhase_sub_factor]
      simp only [map_mul, map_ofNat]
      ring

/-- Chord length is exactly twice the radius times the absolute half-angle sine. -/
theorem modulus_circlePoint_sub (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : 0 ≤ R) (θ₂ θ₁ : SignSequence.FiniteElement.{u}) :
    modulus (circlePoint O R θ₂ - circlePoint O R θ₁) =
      2 * R * |finiteSin (finiteHalf (θ₂ - θ₁))| := by
  rw [circlePoint_sub_factor, modulus_mul, modulus_mul, modulus_ofReal,
    modulus_I, modulus_finitePhase, mul_one, mul_one, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : SignSequence.{u}) ≤ 2), abs_of_nonneg hR]

/-- On a nonzero-radius circle, point equality is exactly equality of the two unit phases. -/
theorem circlePoint_eq_iff_phase_eq (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : R ≠ 0) (θ φ : SignSequence.FiniteElement.{u}) :
    circlePoint O R θ = circlePoint O R φ ↔ finitePhase θ = finitePhase φ := by
  rw [circlePoint, circlePoint, add_right_inj,
    mul_right_inj' ((map_ne_zero ofReal).mpr hR)]

/-- Exactly the ordinary integer multiples of two pi identify finite parameters on a circle. -/
theorem circlePoint_eq_iff_period (O : Surcomplex.{u}) (R : SignSequence.{u})
    (hR : R ≠ 0) (θ φ : SignSequence.FiniteElement.{u}) :
    circlePoint O R θ = circlePoint O R φ ↔
      ∃ n : ℤ, θ.val - φ.val = SignSequence.ofReal ((n : ℝ) * (2 * Real.pi)) := by
  rw [circlePoint_eq_iff_phase_eq O R hR, finitePhase_eq_iff]

end
end Surreal.Surcomplex
