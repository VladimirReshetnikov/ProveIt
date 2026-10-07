/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.FiniteGoodPartTransfer
import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem mean_congr_on_support {f g : X → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.mean f = p.mean g :=
  le_antisymm (p.mean_mono_on_support (fun x hx => (h x hx).le))
    (p.mean_mono_on_support (fun x hx => (h x hx).ge))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

variable {X Y : Type*} (q : X → Y) (S : Set X) (hinj : Set.InjOn q S)

include hinj

theorem restrictedChartDensity_eq_of_values (g : Y → ℝ) (f : X → ℝ)
    (hvalue : ∀ x ∈ S, g (q x) = f x) (hzero : ∀ y ∉ q '' S, g y = 0) :
    g = restrictedChartDensity q S 1 f := by
  funext y
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [restrictedChartDensity_apply q S 1 f hinj hx, one_mul, hvalue x hx]
  · rw [hzero y hy, restrictedChartDensity_zero q S 1 f hy]

theorem restrictedChartDensity_pointwise_comparison (g : Y → ℝ) (f e : X → ℝ)
    (hbound : ∀ x ∈ S, |g (q x) - f x| ≤ e x)
    (hzero : ∀ y ∉ q '' S, g y = 0) (y : Y) :
    |g y - restrictedChartDensity q S 1 f y| ≤ restrictedChartDensity q S 1 e y := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    simpa only [restrictedChartDensity_apply q S 1 f hinj hx,
      restrictedChartDensity_apply q S 1 e hinj hx, one_mul] using hbound x hx
  · rw [hzero y hy, restrictedChartDensity_zero q S 1 f hy,
      restrictedChartDensity_zero q S 1 e hy, sub_self, abs_zero]

theorem restrictedChartDensity_bound (f : X → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x ∈ S, f x ≤ C) (y : Y) : restrictedChartDensity q S 1 f y ≤ C := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    simpa only [restrictedChartDensity_apply q S 1 f hinj hx, one_mul] using hf x hx
  · rw [restrictedChartDensity_zero q S 1 f hy]
    exact hC

theorem restrictedChartDensity_mean_comparison {A : Type*} [Fintype A]
    (weights : FiniteProbabilityWeights A) (g : A → Y → ℝ) (f e : X → ℝ)
    (hbound : ∀ x ∈ S, |weights.mean (fun a => g a (q x)) - f x| ≤ e x)
    (hzero : ∀ a y, y ∉ q '' S → g a y = 0) (y : Y) :
    |weights.mean (fun a => g a y) - restrictedChartDensity q S 1 f y| ≤
      restrictedChartDensity q S 1 e y := by
  apply restrictedChartDensity_pointwise_comparison q S hinj _ f e hbound _ y
  intro y hy
  simp only [hzero _ y hy, weights.mean_const]

end Erdos3

end

section

namespace Erdos3

variable {X Y : Type*} (q : X → Y) (S : Set X) (hinj : Set.InjOn q S)

include hinj

theorem restrictedChartDensity_sub (f g : X → ℝ) :
    (fun y => restrictedChartDensity q S 1 f y - restrictedChartDensity q S 1 g y) =
      restrictedChartDensity q S 1 (fun x => f x - g x) := by
  apply restrictedChartDensity_eq_of_values q S hinj
  · intro x hx
    simp only [restrictedChartDensity_apply q S 1 _ hinj hx, one_mul]
  · intro y hy
    rw [restrictedChartDensity_zero q S 1 f hy, restrictedChartDensity_zero q S 1 g hy, sub_self]

theorem restrictedChartDensity_abs (f : X → ℝ) :
    (fun y => |restrictedChartDensity q S 1 f y|) =
      restrictedChartDensity q S 1 (fun x => |f x|) := by
  apply restrictedChartDensity_eq_of_values q S hinj
  · intro x hx
    simp only [restrictedChartDensity_apply q S 1 _ hinj hx, one_mul]
  · intro y hy
    rw [restrictedChartDensity_zero q S 1 f hy, abs_zero]

theorem restrictedChartDensity_abs_sub (f g : X → ℝ) :
    (fun y => |restrictedChartDensity q S 1 f y - restrictedChartDensity q S 1 g y|) =
      restrictedChartDensity q S 1 (fun x => |f x - g x|) := by
  have hs := restrictedChartDensity_sub q S hinj f g
  simpa only [← hs] using restrictedChartDensity_abs q S hinj (fun x => f x - g x)

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

theorem exists_supported_good_of_bad_lt_one {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (Good : X → Prop)
    (hbad : p.eventProbability (fun x => ¬Good x) < 1) :
    ∃ x, p.weight x ≠ 0 ∧ Good x := by
  by_contra hnone
  have hn (x) (hx : p.weight x ≠ 0) : ¬Good x := fun hg => hnone ⟨x, hx, hg⟩
  have hone : p.eventProbability (fun x => ¬Good x) = 1 := by
    calc
      _ = p.mean (fun _ => 1) := p.mean_congr_on_support (fun x hx => ite_eq_left (hn x hx))
      _ = 1 := p.mean_const 1
  linarith

theorem complexMean_goodPart_exp_error {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (Good : X → Prop)
    (f : X → ℂ) (g : ∀ x, Good x → ℂ) {E : ℝ}
    (hbad : p.eventProbability (fun x => ¬Good x) ≤ Real.exp (-(E + 1)))
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (hgood : ∀ x (hx : Good x), ‖f x - g x hx‖ ≤ Real.exp (-(E + 1))) :
    ‖p.complexMean f - p.complexMean (fun x => if hx : Good x then g x hx else 0)‖ ≤
      Real.exp (-E) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (-(E + 1)) + p.eventProbability (fun x => ¬Good x) :=
      p.complexMean_goodPart_comparison Good f g (Real.exp_pos _).le hf hgood
    _ ≤ 2 * Real.exp (-(E + 1)) := by linarith
    _ ≤ Real.exp 1 * Real.exp (-(E + 1)) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.FiniteProbabilityWeights

end

end OAI
