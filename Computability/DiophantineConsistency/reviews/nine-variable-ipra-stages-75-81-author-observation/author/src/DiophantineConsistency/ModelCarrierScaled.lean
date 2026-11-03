import Mathlib.Tactic.LinearCombination
import DiophantineConsistency.DiscreteOrderedRingFacts
import DiophantineConsistency.Carrier65
/-! # The scaled carrier transfers in a discretely ordered ring

`CarrierScaledAuxiliary118` and `CarrierNormalizedProduct106` prove over `ℤ`
that, at positive inputs, the 66/118 and 67/106 forms have the same zeros as
the maintained Carrier65 polynomial. Their arguments use only positivity,
discreteness, the units `±1` and one congruence modulo four. This module
proves the same zero-set equivalences in every discretely ordered commutative
ring with a residue homomorphism to `ZMod 4`. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelCarrierScaled
open Carrier65 DiscreteOrderedRingFacts

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The 66/118 value, as in `CarrierScaledAuxiliary118.value`. -/
def value118 (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let b := core p v
  b.P*b.Q*((b.delta*b.f^2-b.delta)*(b.V^2-b.y^2)+b.y^2)*b.W*b.Z-b.delta

/-- The 67/106 value, as in `CarrierNormalizedProduct106.value`. -/
def value106 (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let d := core p v
  d.P*d.Q*(d.delta*(d.f^2-1)*(d.V^2-d.y^2)+d.y^2)*d.W*strong d-1

def product (m coefficient gap y s : R) : R := m * (coefficient * gap + y ^ 2) * s - 1

theorem scaled_identity118 (p : Fin 4 → R) (v : Fin 14 → R) :
    value118 p v = (core p v).delta * product
      ((core p v).P*(core p v).Q*(core p v).W)
      ((core p v).delta*((core p v).f^2-1))
      ((core p v).V^2-(core p v).y^2) (core p v).y (strong (core p v)) := by
  dsimp only [value118, product]
  rw [strong_scale]
  ring

theorem original_scaled_identity (p : Fin 4 → R) (v : Fin 14 → R) :
    Carrier65.value p v = (core p v).delta * product
      ((core p v).P*(core p v).Q*(core p v).W)
      ((core p v).delta^2*((core p v).i*(core p v).c^2)^2)
      ((core p v).V^2-(core p v).y^2) (core p v).y (strong (core p v)) := by
  have hU : (core p v).U =
      (core p v).delta^2*((core p v).i*(core p v).c^2)^2*
        ((core p v).V^2-(core p v).y^2)+(core p v).y^2 := by
    change ((core p v).i*(core p v).delta*(core p v).c^2)^2*
      ((core p v).V^2-(core p v).y^2)+(core p v).y^2 = _
    ring
  rw [Carrier65.scaled_identity, hU]
  unfold product
  ring

theorem scaled_identity106 (p : Fin 4 → R) (v : Fin 14 → R) :
    value118 p v = (core p v).delta * value106 p v := by
  dsimp only [value118, value106]
  rw [strong_scale]
  ring

variable (hd : Discrete R)
include hd

theorem q_ge_two (p : Fin 4 → R) (v : Fin 14 → R) (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    2 ≤ (core p v).q := by
  change 2 ≤ p 0 * v 0 + 1
  have := hd _ (mul_pos hb (hv 0))
  linarith

theorem delta_pos (p : Fin 4 → R) (v : Fin 14 → R) (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    0 < (core p v).delta := by
  have hq : 0 < (core p v).q := lt_of_lt_of_le (by norm_num) (q_ge_two hd p v hb hv)
  have hX : 0 < (core p v).X := mul_pos (hv 8) hq
  have hY : 0 < (core p v).Y := mul_pos (hv 7) (pow_pos hq 3)
  have hE : 0 < (core p v).E := mul_pos hX hY
  have ha : 0 < (core p v).a := add_pos hE hY
  rw [delta_shape]
  nlinarith

theorem strong_eq_one {m coefficient gap y s : R}
    (hnegative : s ≠ -1) (h : product m coefficient gap y s = 0) : s = 1 := by
  have hmul : s * (m * (coefficient * gap + y ^ 2)) = 1 := by
    unfold product at h
    linear_combination h
  rcases eq_one_or_neg_one_of_mul_eq_one hd hmul with h1 | h1
  · exact h1
  · exact (hnegative h1).elim

omit hd in
/-- A discriminant one below a square excludes a Pell norm of `-1` modulo 4. -/
theorem strong_ne_neg_one (φ : R →+* ZMod 4) (a f t : R) :
    f ^ 2 - ((a + 2) ^ 2 - 1) * t ^ 2 ≠ -1 := by
  intro h
  have hm := congrArg φ h
  simp only [map_sub, map_mul, map_pow, map_add, map_one, map_neg, map_ofNat] at hm
  have bad : ∀ a f t : ZMod 4, f ^ 2 - ((a + 2) ^ 2 - 1) * t ^ 2 ≠ -1 := by decide
  exact bad _ _ _ hm

theorem replace_coefficient {m δ f t gap y : R}
    (hnegative : f ^ 2 - δ * t ^ 2 ≠ -1) :
    product m (δ ^ 2 * t ^ 2) gap y (f ^ 2 - δ * t ^ 2) = 0 ↔
      product m (δ * (f ^ 2 - 1)) gap y (f ^ 2 - δ * t ^ 2) = 0 := by
  have equal_coefficients (hn : f ^ 2 - δ * t ^ 2 = 1) :
      δ ^ 2 * t ^ 2 = δ * (f ^ 2 - 1) := by
    linear_combination (-δ) * hn
  constructor <;> intro h
  · rwa [← equal_coefficients (strong_eq_one hd hnegative h)]
  · rwa [equal_coefficients (strong_eq_one hd hnegative h)]

/-- The 66/118 form has the Carrier65 zeros at positive inputs. -/
theorem zero_iff118 (φ : R →+* ZMod 4) (p : Fin 4 → R) (v : Fin 14 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value118 p v = 0 ↔ Carrier65.value p v = 0 := by
  have hdelta := (delta_pos hd p v hb hv).ne'
  have hn : (core p v).f^2-(core p v).delta*((core p v).i*(core p v).c^2)^2 ≠ -1 := by
    rw [delta_shape]
    exact strong_ne_neg_one φ _ _ _
  rw [scaled_identity118, original_scaled_identity]
  simp only [mul_eq_zero, hdelta, false_or]
  exact (replace_coefficient hd hn).symm

/-- The 67/106 form has the Carrier65 zeros at positive inputs. -/
theorem zero_iff106 (φ : R →+* ZMod 4) (p : Fin 4 → R) (v : Fin 14 → R)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value106 p v = 0 ↔ Carrier65.value p v = 0 := by
  have hdelta := (delta_pos hd p v hb hv).ne'
  rw [← zero_iff118 hd φ p v hb hv, scaled_identity106, mul_eq_zero]
  simp only [hdelta, false_or]

end DiophantineConsistency.ModelCarrierScaled
