import Surreal.Surcomplex.CayleyInfinitesimal
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Infinite tangent coordinates of finite circle points

This proves `trigonometry:ex:infinitetangent` for actual surcomplex points
and actual finite angles. The example leaves its parameter assumptions
implicit: we retain the preceding tangency regime `0 < τ` with `τ`
infinitesimal. These hypotheses ensure two distinct real intersections
and infinite affine half-angle coordinates. Their points remain finite
and infinitesimally close to the omitted Cayley point `-1`.
-/

universe u

namespace Surreal.Surcomplex.InfiniteTangent

open Foundations

noncomputable section

/-- The positive ordinate appearing in the two circle intersections. -/
def height (τ : SignSequence.{u}) : SignSequence.{u} :=
  SignSequence.sqrt (τ * (2 - τ))

/-- The positive affine half-angle coordinate in the source. -/
def coordinate (τ : SignSequence.{u}) : SignSequence.{u} :=
  SignSequence.sqrt ((2 - τ) / τ)

/-- The intersection above the real axis. -/
def pointPlus (τ : SignSequence.{u}) : Surcomplex.{u} := ⟨-1 + τ, height τ⟩

/-- The intersection below the real axis. -/
def pointMinus (τ : SignSequence.{u}) : Surcomplex.{u} := ⟨-1 + τ, -height τ⟩

@[simp] theorem pointPlus_re (τ : SignSequence.{u}) : (pointPlus τ).re = -1 + τ := rfl
@[simp] theorem pointPlus_im (τ : SignSequence.{u}) : (pointPlus τ).im = height τ := rfl
@[simp] theorem pointMinus_re (τ : SignSequence.{u}) : (pointMinus τ).re = -1 + τ := rfl
@[simp] theorem pointMinus_im (τ : SignSequence.{u}) : (pointMinus τ).im = -height τ := rfl

variable (τ : SignSequence.{u}) (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ)

include hp hi

theorem parameter_lt_one : τ < 1 := by
  have he := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt τ).mp hi 1 zero_lt_one
  simpa only [map_one, abs_of_pos hp] using he

theorem complement_pos : 0 < 2 - τ := by linarith [parameter_lt_one τ hp hi]

theorem height_pos : 0 < height τ :=
  SignSequence.sqrt_pos (mul_pos hp (complement_pos τ hp hi))

@[simp] theorem height_sq : height τ ^ 2 = τ * (2 - τ) :=
  SignSequence.sqrt_sq (mul_pos hp (complement_pos τ hp hi)).le

theorem coordinate_pos : 0 < coordinate τ :=
  SignSequence.sqrt_pos (div_pos (complement_pos τ hp hi) hp)

/-- The square root of the quotient is the ordinate divided by the positive line offset. -/
theorem coordinate_eq_height_div : coordinate τ = height τ / τ := by
  apply SignSequence.sqrt_eq_of_nonneg_sq (div_pos (height_pos τ hp hi) hp).le
  rw [div_pow, height_sq τ hp hi]
  field_simp [hp.ne']

theorem normSq_pointPlus : normSq (pointPlus τ) = 1 := by
  change (-1 + τ) ^ 2 + height τ ^ 2 = 1
  rw [height_sq τ hp hi]
  ring

theorem normSq_pointMinus : normSq (pointMinus τ) = 1 := by
  change (-1 + τ) ^ 2 + (-height τ) ^ 2 = 1
  rw [neg_sq, height_sq τ hp hi]
  ring

/-- The upper displayed intersection lies on the actual unit circle. -/
@[simp] theorem modulus_pointPlus : modulus (pointPlus τ) = 1 := by
  apply modulus_eq_of_nonneg_sq zero_le_one
  simpa only [one_pow] using (normSq_pointPlus τ hp hi).symm

/-- The lower displayed intersection lies on the actual unit circle. -/
@[simp] theorem modulus_pointMinus : modulus (pointMinus τ) = 1 := by
  apply modulus_eq_of_nonneg_sq zero_le_one
  simpa only [one_pow] using (normSq_pointMinus τ hp hi).symm

/-- These are all the intersections of the prescribed line and the actual circle. -/
theorem line_circle_intersection_iff (z : Surcomplex.{u}) :
    modulus z = 1 ∧ z.re = -1 + τ ↔ z = pointPlus τ ∨ z = pointMinus τ := by
  constructor
  · rintro ⟨hm, hr⟩
    have hs := congrArg (fun r : SignSequence.{u} => r ^ 2) hm
    rw [modulus_sq, normSq_eq, hr, one_pow] at hs
    have he : z.im ^ 2 = height τ ^ 2 := by
      rw [height_sq τ hp hi]
      nlinarith only [hs]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
    · exact Or.inl (QuadraticAlgebra.ext hr he)
    · exact Or.inr (QuadraticAlgebra.ext hr he)
  · rintro (rfl | rfl)
    · exact ⟨modulus_pointPlus τ hp hi, rfl⟩
    · exact ⟨modulus_pointMinus τ hp hi, rfl⟩

/-- Positivity of the ordinate distinguishes the two intersections. -/
theorem points_ne : pointPlus τ ≠ pointMinus τ := by
  intro he
  have him := congrArg (fun z : Surcomplex.{u} => z.im) he
  change height τ = -height τ at him
  linarith only [height_pos τ hp hi, him]

omit hi in
theorem pointPlus_ne_neg_one : pointPlus τ ≠ -1 := by
  intro he
  have hr := congrArg (fun z : Surcomplex.{u} => z.re) he
  change -1 + τ = -1 at hr
  linarith only [hp, hr]

omit hi in
theorem pointMinus_ne_neg_one : pointMinus τ ≠ -1 := by
  intro he
  have hr := congrArg (fun z : Surcomplex.{u} => z.re) he
  change -1 + τ = -1 at hr
  linarith only [hp, hr]

/-- The actual inverse Cayley coordinate of the upper point is the displayed positive root. -/
theorem cayleyCoord_pointPlus : cayleyCoord (pointPlus τ) = coordinate τ := by
  change height τ / (1 + (-1 + τ)) = coordinate τ
  rw [show 1 + (-1 + τ) = τ by ring, coordinate_eq_height_div τ hp hi]

/-- The lower point has the opposite actual affine coordinate. -/
theorem cayleyCoord_pointMinus : cayleyCoord (pointMinus τ) = -coordinate τ := by
  change -height τ / (1 + (-1 + τ)) = -coordinate τ
  rw [show 1 + (-1 + τ) = τ by ring, neg_div, coordinate_eq_height_div τ hp hi]

/-- Substitution in the rational chart reconstructs the upper intersection. -/
theorem cayley_coordinate : cayley (coordinate τ) = pointPlus τ := by
  have he := cayley_cayleyCoord
    ⟨pointPlus τ, (mem_unitCircle_iff _).mpr (modulus_pointPlus τ hp hi)⟩
    (pointPlus_ne_neg_one τ hp)
  change cayley (cayleyCoord (pointPlus τ)) = pointPlus τ at he
  rwa [cayleyCoord_pointPlus τ hp hi] at he

/-- Substitution of the negative coordinate reconstructs the lower intersection. -/
theorem cayley_neg_coordinate : cayley (-coordinate τ) = pointMinus τ := by
  have he := cayley_cayleyCoord
    ⟨pointMinus τ, (mem_unitCircle_iff _).mpr (modulus_pointMinus τ hp hi)⟩
    (pointMinus_ne_neg_one τ hp)
  change cayley (cayleyCoord (pointMinus τ)) = pointMinus τ at he
  rwa [cayleyCoord_pointMinus τ hp hi] at he

/-- The ordinate is infinitesimal even though its corresponding affine coordinate is infinite. -/
theorem height_infinitesimal : SignSequence.IsInfinitesimal (height τ) := by
  have htwo : SignSequence.IsFinite (2 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)
  apply SignSequence.infinitesimal_sqrt (mul_pos hp (complement_pos τ hp hi)).le
  exact SignSequence.infinitesimal_mul_finite hi
    (SignSequence.finite_sub htwo (SignSequence.finite_of_infinitesimal hi))

/-- The upper actual point is infinitesimally close to the half-turn point. -/
theorem pointPlus_near_neg_one : IsInfinitesimal (pointPlus τ + 1) := by
  change SignSequence.IsInfinitesimal ((-1 + τ) + 1) ∧
    SignSequence.IsInfinitesimal (height τ + 0)
  rw [show (-1 + τ) + 1 = τ by ring, add_zero]
  exact ⟨hi, height_infinitesimal τ hp hi⟩

/-- The lower actual point is infinitesimally close to the same half-turn point. -/
theorem pointMinus_near_neg_one : IsInfinitesimal (pointMinus τ + 1) := by
  change SignSequence.IsInfinitesimal ((-1 + τ) + 1) ∧
    SignSequence.IsInfinitesimal (-height τ + 0)
  rw [show (-1 + τ) + 1 = τ by ring, add_zero]
  exact ⟨hi, SignSequence.infinitesimal_neg (height_infinitesimal τ hp hi)⟩

/-- The positive half-angle coordinate is an infinite actual surreal number. -/
theorem coordinate_not_finite : ¬ SignSequence.IsFinite (coordinate τ) := by
  apply (infinitesimal_cayley_add_one_iff (coordinate τ)).mp
  rw [cayley_coordinate τ hp hi]
  exact pointPlus_near_neg_one τ hp hi

/-- The negative half-angle coordinate is infinite as well. -/
theorem neg_coordinate_not_finite : ¬ SignSequence.IsFinite (-coordinate τ) := by
  apply (infinitesimal_cayley_add_one_iff (-coordinate τ)).mp
  rw [cayley_neg_coordinate τ hp hi]
  exact pointMinus_near_neg_one τ hp hi

/-- Both circle points have finite actual real and imaginary coordinates. -/
theorem points_finite : IsFinite (pointPlus τ) ∧ IsFinite (pointMinus τ) := by
  rw [← cayley_coordinate τ hp hi, ← cayley_neg_coordinate τ hp hi]
  exact ⟨isFinite_cayley _, isFinite_cayley _⟩

/-- A finite actual angle realizes the upper point and its infinite half-angle tangent. -/
theorem exists_finite_anglePlus : ∃ θ : SignSequence.FiniteElement.{u},
    finitePhase θ = pointPlus τ ∧ finiteTan (finiteHalf θ) = coordinate τ := by
  obtain ⟨θ, hθ⟩ := exists_finitePhase_eq_of_modulus_eq_one
    (pointPlus τ) (modulus_pointPlus τ hp hi)
  refine ⟨θ, hθ, ?_⟩
  rw [← cayleyCoord_finitePhase, hθ, cayleyCoord_pointPlus τ hp hi]

/-- A finite actual angle realizes the lower point and its negative infinite half-angle tangent. -/
theorem exists_finite_angleMinus : ∃ θ : SignSequence.FiniteElement.{u},
    finitePhase θ = pointMinus τ ∧ finiteTan (finiteHalf θ) = -coordinate τ := by
  obtain ⟨θ, hθ⟩ := exists_finitePhase_eq_of_modulus_eq_one
    (pointMinus τ) (modulus_pointMinus τ hp hi)
  refine ⟨θ, hθ, ?_⟩
  rw [← cayleyCoord_finitePhase, hθ, cayleyCoord_pointMinus τ hp hi]

end
end Surreal.Surcomplex.InfiniteTangent
