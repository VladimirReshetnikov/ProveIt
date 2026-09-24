import Surreal.HahnSeries.CoefficientMapping
import Mathlib.Algebra.Group.AddChar

/-!
# Hahn automorphisms from additive characters

The convolution argument underlying `odg:def:lem:twist`.
Every additive character on the exponent group has nonzero values, so
multiplying coefficients by it preserves the full support.
-/

namespace Surreal.HahnSeries
open _root_.HahnSeries Finset
noncomputable section
variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [Field K]

/-- Multiply each Hahn coefficient by a multiplicative character of its exponent. -/
def twist (χ : AddChar Γ K) (x : K⟦Γ⟧) : K⟦Γ⟧ where
  coeff a := x.coeff a * χ a
  isPWO_support' := x.isPWO_support.mono (by
    intro a ha hx
    exact ha (by change x.coeff a * χ a = 0; rw [hx, zero_mul]))

@[simp] theorem coeff_twist (χ : AddChar Γ K) (x : K⟦Γ⟧) (a : Γ) :
    (twist χ x).coeff a = x.coeff a * χ a := rfl

@[simp] theorem support_twist (χ : AddChar Γ K) (x : K⟦Γ⟧) :
    (twist χ x).support = x.support := by
  ext a
  have hn : χ a ≠ 0 := (χ.val_isUnit a).ne_zero
  simp only [mem_support, coeff_twist, mul_ne_zero_iff]
  exact ⟨And.left, fun h => ⟨h, hn⟩⟩

variable [IsOrderedAddMonoid Γ]

theorem twist_mul (χ : AddChar Γ K) (x y : K⟦Γ⟧) : twist χ (x * y) = twist χ x * twist χ y := by
  apply _root_.HahnSeries.ext
  funext a
  have hs : antidiagonal (twist χ x).isPWO_support (twist χ y).isPWO_support a =
      antidiagonal x.isPWO_support y.isPWO_support a := by
    ext p
    simp only [Finset.mem_antidiagonal, support_twist]
  rw [coeff_twist, coeff_mul, coeff_mul, hs, sum_mul]
  apply sum_congr rfl
  intro p hp
  have he : p.1 + p.2 = a := (Finset.mem_antidiagonal.mp hp).2.2
  rw [coeff_twist, coeff_twist, ← he, χ.map_add_eq_mul]
  ring

omit [IsOrderedAddMonoid Γ] in
@[simp] theorem twist_inverse (χ : AddChar Γ K) (x : K⟦Γ⟧) : twist χ⁻¹ (twist χ x) = x := by
  apply _root_.HahnSeries.ext
  funext a
  rw [coeff_twist, coeff_twist, AddChar.inv_apply', mul_assoc,
    mul_inv_cancel₀ (χ.val_isUnit a).ne_zero, mul_one]

/-- Character twisting is a field automorphism, with reciprocal character as inverse. -/
def characterTwist (χ : AddChar Γ K) : K⟦Γ⟧ ≃+* K⟦Γ⟧ where
  toFun := twist χ
  invFun := twist χ⁻¹
  left_inv := twist_inverse χ
  right_inv x := by simpa only [inv_inv] using twist_inverse χ⁻¹ x
  map_mul' := twist_mul χ
  map_add' x y := by
    apply _root_.HahnSeries.ext
    funext a
    simp only [coeff_twist, coeff_add, add_mul]

@[simp] theorem characterTwist_single (χ : AddChar Γ K) (a : Γ) (c : K) :
    characterTwist χ (single a c) = single a (c * χ a) := by
  apply _root_.HahnSeries.ext
  funext b
  change (twist χ (single a c)).coeff b = _
  rw [coeff_twist]
  by_cases hb : b = a
  · subst b; simp only [coeff_single_same]
  · simp only [coeff_single_of_ne hb, zero_mul]

@[simp] theorem characterTwist_C (χ : AddChar Γ K) (c : K) :
    characterTwist χ (C c) = C c := by
  change characterTwist χ (single 0 c) = single 0 c
  rw [characterTwist_single, AddChar.map_zero_eq_one, mul_one]

end
end Surreal.HahnSeries
