import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Valuations on a multiplicative monomial family

Generic steps in `osq:nm:thm:valuation`: a valuation restricted to
nonzero monomials is an additive exponent map. Nonnegative values on
positive exponents make that map monotone. If every field element has
nonnegative value, inversion forces the valuation to be trivial.
-/

namespace Surreal.MonomialValuationObstruction
noncomputable section

variable {E F G : Type*} [AddCommGroup E] [Field F]
  [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- Restriction of an additive valuation to a native monomial homomorphism into field units. -/
def exponentValue (v : AddValuation F (WithTop G)) (m : Multiplicative E →* Fˣ) : E →+ G :=
  AddMonoidHom.mk' (fun x => (v (m (Multiplicative.ofAdd x) : F)).untop
    (v.ne_top_iff.mpr (Units.ne_zero _))) fun x y => by
      rw [WithTop.untop_eq_iff, WithTop.coe_add, WithTop.coe_untop, WithTop.coe_untop]
      change v ((m (Multiplicative.ofAdd x * Multiplicative.ofAdd y)) : F) = _
      rw [map_mul, Units.val_mul, v.map_mul]

/-- The exponent map has exactly the original monomial valuation, viewed in the finite-value group. -/
theorem coe_exponentValue (v : AddValuation F (WithTop G)) (m : Multiplicative E →* Fˣ) (x : E) :
    (exponentValue v m x : WithTop G) = v (m (Multiplicative.ofAdd x) : F) :=
  WithTop.coe_untop _ _

/-- Nonnegativity on positive monomials suffices for monotonicity of the exponent map. -/
theorem exponentValue_monotone [LinearOrder E] [IsOrderedAddMonoid E]
    (v : AddValuation F (WithTop G)) (m : Multiplicative E →* Fˣ)
    (hpos : ∀ x : E, 0 < x → 0 ≤ v (m (Multiplicative.ofAdd x) : F)) :
    Monotone (exponentValue v m) := by
  have hn (x : E) (hx : 0 ≤ x) : 0 ≤ exponentValue v m x := by
    rcases eq_or_lt_of_le hx with he | hp
    · simp [← he]
    · apply WithTop.coe_le_coe.mp
      simpa only [WithTop.coe_zero, coe_exponentValue] using hpos x hp
  intro x y hxy
  have h := hn (y - x) (sub_nonneg.mpr hxy)
  rwa [map_sub, sub_nonneg] at h

/-- If a field valuation is everywhere nonnegative, every nonzero element has value zero. -/
theorem eq_zero_of_nonneg (v : AddValuation F (WithTop G))
    (h : ∀ x : F, 0 ≤ v x) (x : F) (hx : x ≠ 0) : v x = 0 := by
  apply le_antisymm _ (h x)
  calc
    v x ≤ v x + v x⁻¹ := le_add_of_nonneg_right (h x⁻¹)
    _ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]

end
end Surreal.MonomialValuationObstruction
