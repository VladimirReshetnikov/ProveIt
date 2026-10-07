/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Probability.IntervalDivisorProbability

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem exists_weight_pos (p : FiniteProbabilityWeights Ω) : ∃ x, 0 < p.weight x := by
  by_contra h
  push Not at h
  have hs : (∑ x, p.weight x) ≤ 0 := Finset.sum_nonpos (fun x _ => h x)
  rw [p.total] at hs
  norm_num at hs

theorem exists_weight_ne_zero (p : FiniteProbabilityWeights Ω) : ∃ x, p.weight x ≠ 0 := by
  obtain ⟨x, hx⟩ := p.exists_weight_pos
  exact ⟨x, hx.ne'⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem complexMean_goodPart_comparison {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (Good : X → Prop)
    (f : X → ℂ) (g : ∀ x, Good x → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hgood : ∀ x (hx : Good x), ‖f x - g x hx‖ ≤ ε) :
    ‖p.complexMean f - p.complexMean (fun x => if hx : Good x then g x hx else 0)‖ ≤
      ε + p.eventProbability (fun x => ¬Good x) := by
  have hpoint (x : X) :
      ‖f x - (if hx : Good x then g x hx else 0)‖ ≤ ε + if ¬Good x then 1 else 0 := by
    by_cases hx : Good x
    · simpa only [hx, dite_eq_left, not_true_eq_false, ite_false, add_zero] using hgood x hx
    · simpa only [hx, dite_eq_right, not_false_eq_true, ite_true, sub_zero] using
        (hf x).trans (by linarith : (1 : ℝ) ≤ ε + 1)
  apply (p.norm_complexMean_sub_le _ _ _ (fun x _ => hpoint x)).trans_eq
  unfold eventProbability mean
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, p.total, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : Good x <;> simp [hx]

noncomputable def goodPartBaseMean {X B : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (bases : Finset B) (Good : X → Prop)
    (reference : ∀ x, Good x → B → ℂ) : ℂ :=
  p.complexMean (fun x => if hx : Good x then 𝔼 base ∈ bases, reference x hx base else 0)

theorem complexMean_goodPart_base_comparison {X B : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (bases : Finset B) (hbases : bases.Nonempty)
    (Good : X → Prop) (f : X → B → ℂ) (reference : ∀ x, Good x → B → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (hf : ∀ x, ‖𝔼 base ∈ bases, f x base‖ ≤ 1)
    (hgood : ∀ x (hx : Good x) base, base ∈ bases → ‖f x base - reference x hx base‖ ≤ ε) :
    ‖p.complexMean (fun x => 𝔼 base ∈ bases, f x base) -
      p.goodPartBaseMean bases Good reference‖ ≤ ε + p.eventProbability (fun x => ¬Good x) := by
  apply p.complexMean_goodPart_comparison Good _ _ hε hf
  intro x hx
  have h := (uniformFinset bases hbases).norm_complexMean_sub_le
    (fun base => f x base.val) (fun base => reference x hx base.val) (fun _ => ε)
    (fun base _ => hgood x hx base.val base.property)
  rw [uniformFinset_complexMean bases hbases (f x),
    uniformFinset_complexMean bases hbases (reference x hx), mean_const] at h
  exact h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem complexMean_div (p : FiniteProbabilityWeights X) (f : X → ℂ) (z : ℂ) :
    p.complexMean (fun x => f x / z) = p.complexMean f / z := by
  simp only [complexMean, mul_div_assoc, Finset.sum_div]

theorem exists_positive_weight_ge_mean (p : FiniteProbabilityWeights X) (f : X → ℝ) :
    ∃ x, 0 < p.weight x ∧ p.mean f ≤ f x := by
  let A := Finset.univ.filter (fun x => 0 < p.weight x)
  have hA : A.Nonempty := by
    obtain ⟨x, hx⟩ := p.exists_weight_pos
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  obtain ⟨x, hx, hmax⟩ := A.exists_max_image f hA
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  calc
    p.mean f ≤ p.mean (fun _ => f x) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : 0 < p.weight y
      · exact mul_le_mul_of_nonneg_left
          (hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)) hy.le
      · have hz : p.weight y = 0 := le_antisymm (le_of_not_gt hy) (p.nonneg y)
        simp only [hz, zero_mul, le_refl]
    _ = f x := p.mean_const _

theorem exists_positive_weight_ge_complexMean_re (p : FiniteProbabilityWeights X) (f : X → ℂ) :
    ∃ x, 0 < p.weight x ∧ (p.complexMean f).re ≤ (f x).re := by
  rw [p.complexMean_re]
  exact p.exists_positive_weight_ge_mean _

theorem exists_good_base_of_le_re {B : Type*} (p : FiniteProbabilityWeights X)
    (bases : Finset B) (hbases : bases.Nonempty) (Good : X → Prop)
    (f : ∀ x, Good x → B → ℂ) {η : ℝ} (hη : 0 < η)
    (hmean : η ≤ (p.goodPartBaseMean bases Good f).re) :
    ∃ (x : X) (hx : Good x) (b : B),
      0 < p.weight x ∧ b ∈ bases ∧ η ≤ (f x hx b).re := by
  obtain ⟨x, hx, hhigh⟩ := p.exists_positive_weight_ge_complexMean_re
    (fun x => if hx : Good x then 𝔼 b ∈ bases, f x hx b else 0)
  have hselected := hmean.trans hhigh
  by_cases hg : Good x
  · simp only [hg, dite_true] at hselected
    rw [← uniformFinset_complexMean bases hbases (f x hg)] at hselected
    obtain ⟨b, _, hb⟩ := (uniformFinset bases hbases).exists_positive_weight_ge_complexMean_re
      (fun b => f x hg b.val)
    exact ⟨x, hg, b.val, hx, b.property, hselected.trans hb⟩
  · simp only [hg, dite_false, Complex.zero_re] at hselected
    exact (not_le_of_gt hη hselected).elim

theorem exists_normalized_good_cell_of_le_re {B : Type*}
    (p : FiniteProbabilityWeights X) (bases : Finset B) (hbases : bases.Nonempty)
    (Good : X → Prop)
    {R : ∀ x, Good x → B → Type*} [∀ x hx b, Fintype (R x hx b)]
    {C : ∀ x hx b, R x hx b → Type*} [∀ x hx b r, Fintype (C x hx b r)]
    (residue : ∀ x hx b, FiniteProbabilityWeights (R x hx b))
    (cell : ∀ x hx b r, FiniteProbabilityWeights (C x hx b r))
    (value : ∀ x hx b r, C x hx b r → ℂ) (Z : ℂ)
    {η : ℝ} (hη : 0 < η)
    (hmean : η ≤ (p.goodPartBaseMean bases Good (fun x hx b =>
      (residue x hx b).complexMean (fun r =>
        (cell x hx b r).complexMean (value x hx b r)) / Z)).re) :
    ∃ (x : X) (hx : Good x) (b : B) (r : R x hx b) (c : C x hx b r),
      0 < p.weight x ∧ b ∈ bases ∧ 0 < (residue x hx b).weight r ∧
      0 < (cell x hx b r).weight c ∧ η ≤ (value x hx b r c / Z).re := by
  obtain ⟨x, hx, b, hpx, hb, hvalue⟩ :=
    p.exists_good_base_of_le_re bases hbases Good _ hη hmean
  rw [← complexMean_div] at hvalue
  obtain ⟨r, hr, hvr⟩ := (residue x hx b).exists_positive_weight_ge_complexMean_re
    (fun r => (cell x hx b r).complexMean (value x hx b r) / Z)
  have hcell := hvalue.trans hvr
  rw [← complexMean_div] at hcell
  obtain ⟨c, hc, hvc⟩ := (cell x hx b r).exists_positive_weight_ge_complexMean_re
    (fun c => value x hx b r c / Z)
  exact ⟨x, hx, b, r, c, hpx, hb, hr, hc, hcell.trans hvc⟩

theorem exists_good_base_of_comparison {B : Type*}
    (p : FiniteProbabilityWeights X) (bases : Finset B) (hbases : bases.Nonempty)
    (Good : X → Prop) (f : ∀ x, Good x → B → ℂ)
    {source : ℂ} {δ ε : ℝ} (hδ : 0 < δ)
    (hcomparison : ‖source - p.goodPartBaseMean bases Good f‖ ≤ ε)
    (hsource : δ + ε ≤ source.re) :
    ∃ (x : X) (hx : Good x) (b : B),
      0 < p.weight x ∧ b ∈ bases ∧ δ ≤ (f x hx b).re := by
  apply p.exists_good_base_of_le_re bases hbases Good f hδ
  have herror := (Complex.re_le_norm (source - p.goodPartBaseMean bases Good f)).trans
    hcomparison
  rw [Complex.sub_re] at herror
  linarith

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem goodPartBaseMean_sub_norm_le {X B : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (bases : Finset B) (hbases : bases.Nonempty)
    (Good : X → Prop) (f g : ∀ x, Good x → B → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ x (hx : Good x) b, b ∈ bases → ‖f x hx b - g x hx b‖ ≤ ε) :
    ‖p.goodPartBaseMean bases Good f - p.goodPartBaseMean bases Good g‖ ≤ ε := by
  unfold goodPartBaseMean
  apply (p.norm_complexMean_sub_le _ _ (fun _ => ε) ?_).trans_eq (p.mean_const ε)
  intro x _
  by_cases hx : Good x
  · simp only [hx, dite_true]
    have h := (uniformFinset bases hbases).norm_complexMean_sub_le
      (fun b => f x hx b.val) (fun b => g x hx b.val) (fun _ => ε)
      (fun b _ => hgood x hx b.val b.property)
    rw [uniformFinset_complexMean bases hbases (f x hx),
      uniformFinset_complexMean bases hbases (g x hx), mean_const] at h
    exact h
  · simpa only [hx, dite_false, sub_self, norm_zero] using hε

theorem complexMean_goodPart_base_transfer {X B : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (bases : Finset B) (hbases : bases.Nonempty)
    (Good : X → Prop) (source : X → B → ℂ) (reference target : ∀ x, Good x → B → ℂ)
    {A ε : ℝ} (hε : 0 ≤ ε)
    (hsource : ‖p.complexMean (fun x => 𝔼 b ∈ bases, source x b) -
      p.goodPartBaseMean bases Good reference‖ ≤ A)
    (hgood : ∀ x (hx : Good x) b, b ∈ bases → ‖reference x hx b - target x hx b‖ ≤ ε) :
    ‖p.complexMean (fun x => 𝔼 b ∈ bases, source x b) -
      p.goodPartBaseMean bases Good target‖ ≤ A + ε := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hsource
    (p.goodPartBaseMean_sub_norm_le bases hbases Good reference target hε hgood))

end Erdos3.FiniteProbabilityWeights

end

end OAI
