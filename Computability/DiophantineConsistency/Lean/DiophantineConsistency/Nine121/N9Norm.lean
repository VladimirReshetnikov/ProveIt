import DiophantineConsistency.ModelRelationCombining
import Mathlib.Tactic.LinearCombination

/-! # The two-root norm of the nine-variable finalizers

`norm2 θ ω a b = (θ² − ω²(a + b))² − 4ω⁴ab` is the product of the four
conjugates `θ ∓ ω(√a ± √b)` (`norm2_factor`). In an ordered commutative ring:

* outside the sum of two strict majorants the norm is positive
  (`norm2_pos_of_nonpos_scale`, the margin-first step of
  `MarginFinalizer.norm_pos_of_nonpositive_scale`, without `omega`);
* in the ring of differences of a model of `𝗜𝚺₁` a zero with `ω ≠ 0` and
  separated radicands has square radicands and `θ = ω(r + s)`
  (`roots_of_norm2_zero`): the rational-root argument becomes the internal
  `ModelRelationCombining.sq_dvd_sq`. -/
set_option autoImplicit false
noncomputable section
namespace Nine121.N9Norm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing

section Ring
variable {R : Type*} [CommRing R]

def norm2 (θ ω a b : R) : R := (θ ^ 2 - ω ^ 2 * (a + b)) ^ 2 - 4 * ω ^ 4 * a * b

theorem norm2_eq (θ ω a b : R) :
    norm2 θ ω a b = (θ ^ 2 + ω ^ 2 * a - ω ^ 2 * b) ^ 2 - 4 * θ ^ 2 * ω ^ 2 * a := by
  unfold norm2; ring

theorem norm2_factor (θ ω r s : R) :
    norm2 θ ω (r ^ 2) (s ^ 2) =
      (θ - ω * (r + s)) * (θ - ω * (r - s)) * (θ + ω * (r - s)) * (θ + ω * (r + s)) := by
  unfold norm2; ring

theorem norm2_zero_of_root (ω r s : R) : norm2 (ω * (r + s)) ω (r ^ 2) (s ^ 2) = 0 := by
  rw [norm2_factor]; ring

end Ring

section Order
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Outside the sum of two strict majorants the norm is positive. -/
theorem norm2_pos_of_nonpos_scale {a b U W ω E : DiffRing V}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hU : 0 < U) (hV : 0 < W)
    (haU : a < U ^ 2) (hbV : b < W ^ 2) (hω : ω ≤ 0) (hE : 0 < E) :
    0 < norm2 (E - ω * (U + W)) ω a b := by
  set θ := E - ω * (U + W) with hθ
  have hbase : 0 ≤ -ω * (U + W) := mul_nonneg (neg_nonneg.mpr hω) (le_of_lt (add_pos hU hV))
  have hθ' : -ω * (U + W) < θ := by rw [hθ]; linarith
  have hθ0 : 0 < θ := by linarith
  have hsq : (-ω * (U + W)) ^ 2 < θ ^ 2 := by
    have := mul_pos (sub_pos.mpr hθ') (by linarith : 0 < θ + -ω * (U + W))
    nlinarith
  have hrad : ω ^ 2 * (a + b) ≤ ω ^ 2 * (U ^ 2 + W ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg ω)
  have hgap : 2 * ω ^ 2 * U * W < θ ^ 2 - ω ^ 2 * (a + b) := by
    have e : (-ω * (U + W)) ^ 2 = ω ^ 2 * (U ^ 2 + W ^ 2) + 2 * ω ^ 2 * U * W := by ring
    linarith
  have hgap0 : 0 ≤ 2 * ω ^ 2 * U * W := by
    have := sq_nonneg ω; have := hU.le; have := hV.le; positivity
  have hgapSq : (2 * ω ^ 2 * U * W) ^ 2 < (θ ^ 2 - ω ^ 2 * (a + b)) ^ 2 := by
    have := mul_pos (sub_pos.mpr hgap) (by linarith : 0 < θ ^ 2 - ω ^ 2 * (a + b) + 2 * ω ^ 2 * U * W)
    nlinarith
  have hprod : a * b ≤ U ^ 2 * W ^ 2 := mul_le_mul (le_of_lt haU) (le_of_lt hbV) hb (sq_nonneg U)
  have hω4 : 0 ≤ 4 * ω ^ 4 := by positivity
  have hprod' := mul_le_mul_of_nonneg_left hprod hω4
  have e2 : (2 * ω ^ 2 * U * W) ^ 2 = 4 * ω ^ 4 * (U ^ 2 * W ^ 2) := by ring
  unfold norm2
  have e3 : 4 * ω ^ 4 * a * b = 4 * ω ^ 4 * (a * b) := by ring
  rw [e3]
  linarith

end Order

section Model
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem sq_eq_sq_cases {x y : DiffRing V} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x - y) * (x + y) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

private theorem root_of_sq_mul {m X a : DiffRing V} (hm : m ≠ 0) (h : X ^ 2 = m ^ 2 * a) :
    ∃ r, a = r ^ 2 ∧ X = m * r := by
  have hd : m ^ 2 ∣ X ^ 2 := ⟨a, h⟩
  obtain ⟨r, hr⟩ := ModelRelationCombining.sq_dvd_sq m X hm hd
  refine ⟨r, ?_, hr⟩
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  apply mul_left_cancel₀ hm2
  rw [← h, hr]; ring

/-- **Roots of a separated norm zero**, in the ring of differences. -/
theorem roots_of_norm2_zero {θ ω a b : DiffRing V} (hω : ω ≠ 0) (hab : a ≠ b)
    (h : norm2 θ ω a b = 0) : ∃ r s, a = r ^ 2 ∧ b = s ^ 2 ∧ θ = ω * (r + s) := by
  rw [norm2_eq] at h
  obtain ⟨X, hX⟩ : ∃ X, X = θ ^ 2 + ω ^ 2 * a - ω ^ 2 * b := ⟨_, rfl⟩
  rw [← hX] at h
  have hX2 : X ^ 2 = (2 * θ * ω) ^ 2 * a := by linear_combination h
  have hθ : θ ≠ 0 := by
    intro h0
    rw [h0] at hX2
    have hX0 : X = 0 := by
      have : X ^ 2 = 0 := by rw [hX2]; ring
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    rw [hX, h0] at hX0
    have : ω ^ 2 * (a - b) = 0 := by linear_combination hX0
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hω (pow_eq_zero_iff two_ne_zero |>.mp h1)
    · exact hab (by linear_combination h1)
  have hm : 2 * θ * ω ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hθ) hω
  obtain ⟨r, har, hXr⟩ := root_of_sq_mul hm hX2
  -- `(θ − ωr)² = ω² b`
  have hY : (θ - ω * r) ^ 2 = ω ^ 2 * b := by
    have : X = 2 * θ * ω * r := hXr
    rw [hX, har] at this
    linear_combination this
  obtain ⟨s, hbs, hYs⟩ := root_of_sq_mul hω hY
  exact ⟨r, s, har, hbs, by linear_combination hYs⟩

end Model

end Nine121.N9Norm

#print axioms Nine121.N9Norm.norm2_pos_of_nonpos_scale
#print axioms Nine121.N9Norm.roots_of_norm2_zero
