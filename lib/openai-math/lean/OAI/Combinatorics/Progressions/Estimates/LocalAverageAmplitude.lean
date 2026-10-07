import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
import OAI.Combinatorics.Progressions.Geometry.FiniteSupportTranslation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_weighted_test_summable {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) (f : X → ℂ) : Summable (fun x => (w x : ℂ) * f x) := by
  apply (hasSum_sum_of_ne_finset_zero (s := S) _).summable
  intro x hx
  simp only [hw x hx, Complex.ofReal_zero, zero_mul]

theorem finite_weighted_test_norm_le {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖∑' x, (w x : ℂ) * f x‖ ≤ ∑' x, |w x| := by
  have hs : Summable (fun x => |w x|) :=
    (hasSum_sum_of_ne_finset_zero (s := S) (fun x hx => by rw [hw x hx, abs_zero])).summable
  apply tsum_of_norm_bounded hs.hasSum
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)).trans_eq (mul_one _)

theorem finite_weighted_translation_test_le {G : Type*} [AddCommGroup G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (v : G) :
    ‖(∑' x, (w x : ℂ) * f (x + v)) - ∑' x, (w x : ℂ) * f x‖ ≤
      ∑' x, |w (x - v) - w x| := by
  classical
  have hshift (x : G) (hx : x ∉ S.image (fun y => y + v)) : w (x - v) = 0 := by
    apply hw
    intro hy
    exact hx (Finset.mem_image.mpr ⟨x - v, hy, sub_add_cancel x v⟩)
  have hleft : (∑' x, (w x : ℂ) * f (x + v)) = ∑' x, (w (x - v) : ℂ) * f x := by
    simpa using (Equiv.addRight v).tsum_eq (fun x => (w (x - v) : ℂ) * f x)
  have he : (∑' x, (w x : ℂ) * f (x + v)) - ∑' x, (w x : ℂ) * f x =
      ∑' x, ((w (x - v) - w x : ℝ) : ℂ) * f x := by
    rw [hleft, ← (finite_weighted_test_summable _ _ hshift f).tsum_sub
      (finite_weighted_test_summable w S hw f)]
    apply tsum_congr
    intro x
    rw [Complex.ofReal_sub, sub_mul]
  rw [he]
  exact finite_weighted_test_norm_le _ (S ∪ S.image (fun y => y + v))
    (translation_difference_zero_off w S hw v) f hf

theorem normalized_finite_translation_test_le {G : Type*} [AddCommGroup G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (v : G) {Z : ℝ} (hZ : 0 < Z) :
    ‖(∑' x, ((w x / Z : ℝ) : ℂ) * f (x + v)) -
      ∑' x, ((w x / Z : ℝ) : ℂ) * f x‖ ≤ (∑' x, |w (x - v) - w x|) / Z := by
  have h := finite_weighted_translation_test_le (fun x => w x / Z) S
    (fun x hx => by rw [hw x hx, zero_div]) f hf v
  simpa only [← sub_div, abs_div, abs_of_pos hZ, tsum_div_const] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_weighted_expect_comm {G X : Type*} [Fintype X]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0) (F : X → G → ℂ) :
    (𝔼 u, ∑' x, (w x : ℂ) * F u x) = ∑' x, (w x : ℂ) * (𝔼 u, F u x) := by
  have ht (f : G → ℂ) : (∑' x, (w x : ℂ) * f x) = ∑ x ∈ S, (w x : ℂ) * f x := by
    apply (hasSum_sum_of_ne_finset_zero (s := S) _).tsum_eq
    intro x hx
    simp only [hw x hx, Complex.ofReal_zero, zero_mul]
  simp_rw [ht]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.mul_expect _ _ _).symm

theorem finite_probability_test_norm_le {G : Type*}
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∑' x, w x) = 1)
    (f : G → ℂ) {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    ‖∑' x, (w x : ℂ) * f x‖ ≤ B := by
  have hs : Summable w := (hasSum_sum_of_ne_finset_zero hw).summable
  have hm : HasSum (fun x => w x * B) B := by
    simpa only [hmass, one_mul] using hs.hasSum.mul_right B
  apply tsum_of_norm_bounded hm
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
  exact mul_le_mul_of_nonneg_left (hf x) (hw0 x)

theorem finite_probability_shift_transfer {G X : Type*} [AddCommGroup G]
    [Fintype X] [Nonempty X]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∑' x, w x) = 1)
    (shift : X → G) (f : G → ℂ) {ε B : ℝ}
    (hmove : ∀ u, ‖(∑' x, (w x : ℂ) * f (x + shift u)) -
      ∑' x, (w x : ℂ) * f x‖ ≤ ε)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ B) :
    ‖∑' x, (w x : ℂ) * f x‖ ≤ ε + B := by
  let base := ∑' x, (w x : ℂ) * f x
  let mean := 𝔼 u, ∑' x, (w x : ℂ) * f (x + shift u)
  have he : mean - base = 𝔼 u, ((∑' x, (w x : ℂ) * f (x + shift u)) - base) := by
    rw [Finset.expect_sub_distrib, Fintype.expect_const]
  have hdiff : ‖mean - base‖ ≤ ε := by
    rw [he]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun u _ => hmove u)).trans_eq (Fintype.expect_const ε)
  have hmean : ‖mean‖ ≤ B := by
    dsimp only [mean]
    rw [finite_weighted_expect_comm w S hw]
    exact finite_probability_test_norm_le w S hw hw0 hmass _ hlocal
  calc
    ‖base‖ = ‖(base - mean) + mean‖ := by rw [sub_add_cancel]
    _ ≤ ‖base - mean‖ + ‖mean‖ := norm_add_le _ _
    _ ≤ ε + B := add_le_add (by simpa only [norm_sub_rev] using hdiff) hmean

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem norm_local_average_amplitude_le {G X : Type*} [Fintype X] [Nonempty X]
    (point : X → G) (f amplitude : G → ℂ) (base : G)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hamp : ‖amplitude base‖ ≤ 1)
    {η β : ℝ} (hvariation : ∀ u, ‖amplitude (point u) - amplitude base‖ ≤ η)
    (hlocal : ‖𝔼 u, f (point u)‖ ≤ β) :
    ‖𝔼 u, amplitude (point u) * f (point u)‖ ≤ η + β := by
  have he : (𝔼 u, amplitude (point u) * f (point u)) =
      (𝔼 u, (amplitude (point u) - amplitude base) * f (point u)) +
        amplitude base * (𝔼 u, f (point u)) := by
    rw [Finset.mul_expect, ← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro u _
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect (fun u _ => ?_)).trans_eq (Fintype.expect_const η)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)).trans (by simpa using hvariation u)
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hamp (norm_nonneg _)).trans (by simpa using hlocal)

end Erdos3

end

end OAI
