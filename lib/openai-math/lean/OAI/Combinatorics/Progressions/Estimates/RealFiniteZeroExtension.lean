/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def zeroExtendFinset {X : Type*} (S : Finset X) (f : X → ℂ) (x : X) : ℂ := by
  classical
  exact if x ∈ S then f x else 0

theorem expect_finset_subtype {X : Type*} (S : Finset X) (f : X → ℂ) :
    (𝔼 x : S, f x.val) = 𝔼 x ∈ S, f x := by
  rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
    Finset.sum_coe_sort]

theorem expect_zeroExtendFinset {X : Type*} (A S : Finset X) (hSA : S ⊆ A) (f : X → ℂ) :
    (𝔼 x ∈ A, zeroExtendFinset S f x) =
      ((S.card : ℂ) / (A.card : ℂ)) * (𝔼 x ∈ S, f x) := by
  classical
  rw [Finset.expect_eq_sum_div_card]
  simp only [zeroExtendFinset, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hSA]
  rw [← Finset.card_mul_expect S f]
  ring

theorem norm_expect_zeroExtendFinset {X : Type*} (A S : Finset X) (hSA : S ⊆ A) (f : X → ℂ) :
    ‖𝔼 x ∈ A, zeroExtendFinset S f x‖ =
      ((S.card : ℝ) / (A.card : ℝ)) * ‖𝔼 x ∈ S, f x‖ := by
  rw [expect_zeroExtendFinset A S hSA f, norm_mul, norm_div,
    Complex.norm_natCast, Complex.norm_natCast]

theorem zeroExtendFinset_mul_left {X : Type*} (S : Finset X) (f g : X → ℂ) (x : X) :
    f x * zeroExtendFinset S g x = zeroExtendFinset S (fun x => f x * g x) x := by
  classical
  by_cases hx : x ∈ S <;> simp [zeroExtendFinset, hx]

theorem zeroExtendFinset_mul_star {X : Type*} [DecidableEq X] (S T : Finset X) (f g : X → ℂ) (x : X) :
    zeroExtendFinset S f x * star (zeroExtendFinset T g x) =
      zeroExtendFinset (S ∩ T) (fun x => f x * star (g x)) x := by
  classical
  by_cases hs : x ∈ S <;> by_cases ht : x ∈ T <;> simp [zeroExtendFinset, hs, ht]

theorem zeroExtendFinset_norm_le_one {X : Type*} (S : Finset X) (f : X → ℂ)
    (hf : ∀ x ∈ S, ‖f x‖ ≤ 1) (x : X) : ‖zeroExtendFinset S f x‖ ≤ 1 := by
  classical
  by_cases hx : x ∈ S
  · simpa [zeroExtendFinset, hx] using hf x hx
  · simp [zeroExtendFinset, hx]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

noncomputable def realZeroExtendFinset {X : Type*} (S : Finset X) (f : X → ℝ) (x : X) : ℝ :=
  if x ∈ S then f x else 0

theorem realZeroExtendFinset_on {X : Type*} (S : Finset X) (f : X → ℝ)
    {x : X} (hx : x ∈ S) : realZeroExtendFinset S f x = f x := by
  simp only [realZeroExtendFinset, ite_eq_left hx]

theorem realZeroExtendFinset_off {X : Type*} (S : Finset X) (f : X → ℝ)
    {x : X} (hx : x ∉ S) : realZeroExtendFinset S f x = 0 := by
  simp only [realZeroExtendFinset, ite_eq_right hx]

theorem realZeroExtendFinset_unit {X : Type*} (S : Finset X) (f : X → ℝ)
    (hf : ∀ x ∈ S, 0 ≤ f x ∧ f x ≤ 1) (x : X) :
    0 ≤ realZeroExtendFinset S f x ∧ realZeroExtendFinset S f x ≤ 1 := by
  by_cases hx : x ∈ S
  · simpa only [realZeroExtendFinset_on S f hx] using hf x hx
  · simp only [realZeroExtendFinset_off S f hx, le_refl, zero_le_one, and_self]

theorem realZeroExtendFinset_eq_complex_re {X : Type*} (S : Finset X) (f : X → ℂ) :
    realZeroExtendFinset S (fun x => (f x).re) = fun x => (zeroExtendFinset S f x).re := by
  funext x
  by_cases hx : x ∈ S <;> simp [realZeroExtendFinset, zeroExtendFinset, hx]

theorem realZeroExtendFinset_mul {X : Type*} (S : Finset X) (f g : X → ℝ) :
    realZeroExtendFinset S (fun x => f x * g x) =
      fun x => f x * realZeroExtendFinset S g x := by
  funext x
  by_cases hx : x ∈ S <;> simp [realZeroExtendFinset, hx]

end Erdos3

end

end OAI
