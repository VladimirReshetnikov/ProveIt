import OAI.Combinatorics.Progressions.Estimates.LipschitzExtensionAlongMap

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_complex_extension_of_distance_bound
    {A Y : Type*} [PseudoMetricSpace Y] (embed : A → Y) (f : A → ℂ) (L B : ℝ≥0)
    (hf : ∀ a b, dist (f a) (f b) ≤ L * dist (embed a) (embed b))
    (hb : ∀ a, ‖f a‖ ≤ B) :
    ∃ g : Y → ℂ, LipschitzWith (2 * L) g ∧ (∀ a, g (embed a) = f a) ∧
      ∀ y, ‖g y‖ ≤ 2 * B := by
  classical
  let S := Set.range embed
  let pre (y : S) : A := Classical.choose y.property
  have hpre (y : S) : embed (pre y) = y.val := Classical.choose_spec y.property
  have hF : LipschitzWith L (fun y : S => f (pre y)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have h := hf (pre y) (pre z)
    rw [hpre y, hpre z] at h
    exact h
  obtain ⟨g, hg, heq, hgb⟩ := exists_complex_extension_from_subset S
    (fun y => f (pre y)) L B hF (fun y => hb (pre y))
  refine ⟨g, hg, ?_, hgb⟩
  intro a
  let y : S := ⟨embed a, ⟨a, rfl⟩⟩
  have hzero : dist (f (pre y)) (f a) ≤ 0 := by
    have h := hf (pre y) a
    rw [hpre y] at h
    simpa only [y, dist_self, mul_zero] using h
  exact (heq y).trans (dist_le_zero.mp hzero)

theorem exists_bounded_extension_on_separated_charts
    {A X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (chart : A → X → Y) (S : Set X) (K D L B : ℝ≥0)
    (hwithin : ∀ a x, x ∈ S → ∀ y, y ∈ S → dist x y ≤ K * dist (chart a x) (chart a y))
    (hsep : ∀ a b, a ≠ b → ∀ x, x ∈ S → ∀ y, y ∈ S →
      (1 : ℝ) ≤ D * dist (chart a x) (chart b y))
    (f : A → X → ℂ) (hf : ∀ a, LipschitzOnWith L (f a) S)
    (hb : ∀ a x, x ∈ S → ‖f a x‖ ≤ B) :
    ∃ g : Y → ℂ, LipschitzWith (2 * max (L * K) (2 * B * D)) g ∧
      (∀ a x, x ∈ S → g (chart a x) = f a x) ∧ ∀ y, ‖g y‖ ≤ 2 * B := by
  let P := {p : A × X // p.2 ∈ S}
  let embed : P → Y := fun p => chart p.val.1 p.val.2
  let F : P → ℂ := fun p => f p.val.1 p.val.2
  let C := max (L * K) (2 * B * D)
  have hLC : ((L * K : ℝ≥0) : ℝ) ≤ C := by exact_mod_cast le_max_left (L * K) (2 * B * D)
  have hDC : ((2 * B * D : ℝ≥0) : ℝ) ≤ C := by exact_mod_cast le_max_right (L * K) (2 * B * D)
  have hF (p q : P) : dist (F p) (F q) ≤ C * dist (embed p) (embed q) := by
    rcases p with ⟨⟨a, x⟩, hx⟩
    rcases q with ⟨⟨b, y⟩, hy⟩
    change dist (f a x) (f b y) ≤ C * dist (chart a x) (chart b y)
    by_cases hab : a = b
    · subst b
      calc
        _ ≤ (L : ℝ) * dist x y := (hf a).dist_le_mul x hx y hy
        _ ≤ (L : ℝ) * (K * dist (chart a x) (chart a y)) :=
          mul_le_mul_of_nonneg_left (hwithin a x hx y hy) L.coe_nonneg
        _ = ((L * K : ℝ≥0) : ℝ) * dist (chart a x) (chart a y) := by
          rw [NNReal.coe_mul, mul_assoc]
        _ ≤ _ := mul_le_mul_of_nonneg_right hLC dist_nonneg
    · have hs := hsep a b hab x hx y hy
      have hn : dist (f a x) (f b y) ≤ 2 * (B : ℝ) := by
        rw [dist_eq_norm]
        exact (norm_sub_le _ _).trans (by linarith [hb a x hx, hb b y hy])
      calc
        _ ≤ 2 * (B : ℝ) := hn
        _ ≤ (2 * (B : ℝ)) * (D * dist (chart a x) (chart b y)) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * (B : ℝ))
        _ = ((2 * B * D : ℝ≥0) : ℝ) * dist (chart a x) (chart b y) := by
          simp only [NNReal.coe_mul, NNReal.coe_ofNat]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hDC dist_nonneg
  obtain ⟨g, hg, heq, hgb⟩ := exists_complex_extension_of_distance_bound embed F C B hF
    (fun p => hb p.val.1 p.val.2 p.property)
  exact ⟨g, hg, fun a x hx => heq ⟨(a, x), hx⟩, hgb⟩

end Erdos3

end

end OAI
