import OAI.Combinatorics.Progressions.Probability.FiniteConditionedMass
import OAI.Combinatorics.Progressions.Probability.NormalizedDensityL1

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def ofPositiveWeights {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) : FiniteProbabilityWeights X where
  weight x := w x / ∑ y, w y
  nonneg x := div_nonneg (hw x) hmass.le
  total := by rw [← Finset.sum_div, div_self hmass.ne']

theorem ofPositiveWeights_mean {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (f : X → ℝ) :
    (ofPositiveWeights w hw hmass).mean f = (∑ x, w x * f x) / ∑ x, w x := by
  simp only [mean, ofPositiveWeights, div_mul_eq_mul_div, Finset.sum_div]

theorem ofPositiveWeights_complexMean {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (f : X → ℂ) :
    (ofPositiveWeights w hw hmass).complexMean f =
      (∑ x, (w x : ℂ) * f x) / ((∑ x, w x : ℝ) : ℂ) := by
  simp only [complexMean, ofPositiveWeights, Complex.ofReal_div, div_mul_eq_mul_div, Finset.sum_div]

theorem ofPositiveWeights_weight_ne_zero {X : Type*} [Fintype X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (x : X) :
    (ofPositiveWeights w hw hmass).weight x ≠ 0 ↔ w x ≠ 0 := by
  change w x / (∑ y, w y) ≠ 0 ↔ w x ≠ 0
  constructor
  · intro h hx
    apply h
    rw [hx, zero_div]
  · intro hx
    exact div_ne_zero hx hmass.ne'

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem norm_complexMean_sub_le_weight_l1 {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.complexMean f - q.complexMean f‖ ≤ ∑ x, |p.weight x - q.weight x| := by
  simp only [complexMean, ← Finset.sum_sub_distrib, ← sub_mul, ← Complex.ofReal_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)).trans_eq (mul_one _)

theorem exists_positive_weight_norm_ge_mean {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (f : X → ℂ) :
    ∃ x, 0 < p.weight x ∧ ‖p.complexMean f‖ ≤ ‖f x‖ := by
  classical
  let A := Finset.univ.filter (fun x => 0 < p.weight x)
  have hA : A.Nonempty := by
    by_contra hn
    have hzero (x : X) : p.weight x = 0 := by
      apply le_antisymm _ (p.nonneg x)
      apply le_of_not_gt
      intro hx
      exact hn ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    have ht := p.total
    simp only [hzero, Finset.sum_const_zero] at ht
    norm_num at ht
  obtain ⟨x, hx, hmax⟩ := A.exists_max_image (fun y => ‖f y‖) hA
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  apply (norm_sum_le _ _).trans
  calc
    (∑ y, ‖(p.weight y : ℂ) * f y‖) = ∑ y, p.weight y * ‖f y‖ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.nonneg y)]
    _ ≤ ∑ y, p.weight y * ‖f x‖ := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : 0 < p.weight y
      · exact mul_le_mul_of_nonneg_left (hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)) hy.le
      · have hz : p.weight y = 0 := le_antisymm (le_of_not_gt hy) (p.nonneg y)
        simp only [hz, zero_mul, le_refl]
    _ = ‖f x‖ := by rw [← Finset.sum_mul, p.total, one_mul]

theorem exists_piece_discrepancy_of_weight_l1 {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (f g : X → ℂ) (hg : ∀ x, ‖g x‖ ≤ 1)
    {η : ℝ} (hweights : (∑ x, |p.weight x - q.weight x|) ≤ η) :
    ∃ x, 0 < p.weight x ∧ ‖p.complexMean f - q.complexMean g‖ - η ≤ ‖f x - g x‖ := by
  obtain ⟨x, hx, hnorm⟩ := p.exists_positive_weight_norm_ge_mean (fun y => f y - g y)
  have heq : p.complexMean (fun y => f y - g y) = p.complexMean f - p.complexMean g := by
    simp only [complexMean, mul_sub, Finset.sum_sub_distrib]
  rw [heq] at hnorm
  have hmove := (norm_complexMean_sub_le_weight_l1 p q g hg).trans hweights
  have htriangle := norm_sub_le_norm_sub_add_norm_sub (p.complexMean f) (p.complexMean g) (q.complexMean g)
  exact ⟨x, hx, by linarith⟩

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators

theorem normalized_finite_weights_l1_le {X : Type*} [Fintype X] (f g : X → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hfMass : 0 < ∑ x, f x) (hgMass : 0 < ∑ x, g x) :
    (∑ x, |f x / (∑ y, f y) - g x / (∑ y, g y)|) ≤
      2 * (∑ x, |f x - g x|) / (∑ x, f x) := by
  let I := ∑ x, f x
  let J := ∑ x, g x
  have hI : 0 < I := hfMass
  have hJ : 0 < J := hgMass
  have hm : |I - J| ≤ ∑ x, |f x - g x| := by
    dsimp only [I, J]
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hpoint (x : X) : |f x / I - g x / J| ≤
      |f x - g x| / I + g x * |1 / I - 1 / J| := by
    have heq : f x / I - g x / J = (f x - g x) / I + g x * (1 / I - 1 / J) := by ring
    rw [heq]
    simpa only [abs_div, abs_of_pos hI, abs_mul, abs_of_nonneg (hg x)] using
      abs_add_le ((f x - g x) / I) (g x * (1 / I - 1 / J))
  calc
    _ ≤ ∑ x, (|f x - g x| / I + g x * |1 / I - 1 / J|) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = (∑ x, |f x - g x|) / I + J * |1 / I - 1 / J| := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    _ = (∑ x, |f x - g x|) / I + |I - J| / I := by
      rw [positive_mass_inverse_difference hI hJ]
    _ ≤ (∑ x, |f x - g x|) / I + (∑ x, |f x - g x|) / I :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hm hI.le)
    _ = 2 * (∑ x, |f x - g x|) / (∑ x, f x) := by dsimp only [I]; ring

theorem finite_weight_mass_pos_of_relative_error {X : Type*} [Fintype X]
    (f g : X → ℝ) (hfMass : 0 < ∑ x, f x) {δ : ℝ} (hδ : δ < 1)
    (herr : ∀ x, |g x - f x| ≤ δ * f x) : 0 < ∑ x, g x := by
  have hlower : (1 - δ) * (∑ x, f x) ≤ ∑ x, g x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have h := (abs_le.mp (herr x)).1
    nlinarith
  exact (mul_pos (sub_pos.mpr hδ) hfMass).trans_le hlower

theorem normalized_finite_weights_l1_relative {X : Type*} [Fintype X] (f g : X → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hfMass : 0 < ∑ x, f x) (hgMass : 0 < ∑ x, g x)
    {δ : ℝ} (herr : ∀ x, |g x - f x| ≤ δ * f x) :
    (∑ x, |f x / (∑ y, f y) - g x / (∑ y, g y)|) ≤ 2 * δ := by
  have he : (∑ x, |f x - g x|) ≤ δ * ∑ x, f x := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    simpa only [abs_sub_comm] using herr x
  apply (normalized_finite_weights_l1_le f g hg hfMass hgMass).trans
  calc
    2 * (∑ x, |f x - g x|) / (∑ x, f x) ≤
        2 * (δ * ∑ x, f x) / (∑ x, f x) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num)) hfMass.le
    _ = 2 * δ := by field_simp

theorem normalized_finite_weights_pair_l1 {X : Type*} [Fintype X] (f g h : X → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hh : ∀ x, 0 ≤ h x)
    (hfMass : 0 < ∑ x, f x) (hgMass : 0 < ∑ x, g x) (hhMass : 0 < ∑ x, h x)
    {δ : ℝ} (hgerr : ∀ x, |g x - f x| ≤ δ * f x) (hherr : ∀ x, |h x - f x| ≤ δ * f x) :
    (∑ x, |g x / (∑ y, g y) - h x / (∑ y, h y)|) ≤ 4 * δ := by
  have hg' := normalized_finite_weights_l1_relative f g hg hfMass hgMass hgerr
  have hh' := normalized_finite_weights_l1_relative f h hh hfMass hhMass hherr
  have ht : (∑ x, |g x / (∑ y, g y) - h x / (∑ y, h y)|) ≤
      (∑ x, |f x / (∑ y, f y) - g x / (∑ y, g y)|) +
      (∑ x, |f x / (∑ y, f y) - h x / (∑ y, h y)|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    simpa only [abs_sub_comm] using
      abs_sub_le (g x / (∑ y, g y)) (f x / (∑ y, f y)) (h x / (∑ y, h y))
  linarith

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eq_of_weight_eq {X : Type*} [Fintype X] {p q : FiniteProbabilityWeights X}
    (h : ∀ x, p.weight x = q.weight x) : p = q := by
  cases p with
  | mk wp hp tp =>
    cases q with
    | mk wq hq tq =>
      have he : wp = wq := funext h
      subst wq
      rfl

theorem ofPositiveWeights_probability {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X) :
    ofPositiveWeights p.weight p.nonneg (by rw [p.total]; norm_num) = p := by
  apply eq_of_weight_eq
  intro x
  change p.weight x / (∑ y, p.weight y) = p.weight x
  rw [p.total, div_one]

def restrictedWeight {X : Type*} [DecidableEq X] (w : X → ℝ) (G : Finset X) (x : X) : ℝ :=
  if x ∈ G then w x else 0

theorem restrictedWeight_nonneg {X : Type*} [DecidableEq X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (G : Finset X) (x : X) : 0 ≤ restrictedWeight w G x := by
  unfold restrictedWeight
  split_ifs
  · exact hw x
  · exact le_rfl

theorem restrictedWeight_total {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ) (G : Finset X) :
    (∑ x, restrictedWeight w G x) = ∑ x ∈ G, w x := by
  simp [restrictedWeight]

theorem ofPositiveWeights_mass {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (G : Finset X) :
    (ofPositiveWeights w hw hmass).mass G = (∑ x ∈ G, w x) / ∑ x, w x := by
  simp only [mass, ofPositiveWeights, Finset.sum_div]

noncomputable def conditionPositiveWeights {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (G : Finset X) (hG : 0 < ∑ x ∈ G, w x) :
    FiniteProbabilityWeights X :=
  (ofPositiveWeights w hw hmass).condition G (by
    rw [ofPositiveWeights_mass]
    exact div_pos hG hmass)

theorem conditionPositiveWeights_weight {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (G : Finset X) (hG : 0 < ∑ x ∈ G, w x) (x : X) :
    (conditionPositiveWeights w hw hmass G hG).weight x = restrictedWeight w G x / ∑ y ∈ G, w y := by
  unfold conditionPositiveWeights condition
  change (if x ∈ G then w x / (∑ y, w y) else 0) / (ofPositiveWeights w hw hmass).mass G =
    restrictedWeight w G x / ∑ y ∈ G, w y
  rw [ofPositiveWeights_mass]
  by_cases hx : x ∈ G
  · simp only [restrictedWeight, hx, ite_true]
    field_simp [hmass.ne', hG.ne']
  · simp only [restrictedWeight, hx, ite_false, zero_div]

theorem conditionPositiveWeights_eq_restricted {X : Type*} [Fintype X] [DecidableEq X] (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (G : Finset X) (hG : 0 < ∑ x ∈ G, w x) :
    conditionPositiveWeights w hw hmass G hG =
      ofPositiveWeights (restrictedWeight w G) (restrictedWeight_nonneg w hw G)
        (by rw [restrictedWeight_total]; exact hG) := by
  apply eq_of_weight_eq
  intro x
  rw [conditionPositiveWeights_weight]
  change restrictedWeight w G x / (∑ y ∈ G, w y) =
    restrictedWeight w G x / (∑ y, restrictedWeight w G y)
  rw [restrictedWeight_total]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem ofPositiveWeights_complexMean_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (w : X → ℝ) (v : Y → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (htotal : 0 < ∑ x, w x) (vtotal : 0 < ∑ y, v y) (he : ∀ x, w x = v (e x))
    (f : X → ℂ) (g : Y → ℂ) (hfg : ∀ x, f x = g (e x)) :
    (ofPositiveWeights w hw htotal).complexMean f = (ofPositiveWeights v hv vtotal).complexMean g := by
  rw [ofPositiveWeights_complexMean, ofPositiveWeights_complexMean]
  have hsum : (∑ x, w x) = ∑ y, v y := Fintype.sum_equiv e _ _ he
  have hnum : (∑ x, (w x : ℂ) * f x) = ∑ y, (v y : ℂ) * g y := by
    apply Fintype.sum_equiv e
    intro x
    rw [he x, hfg x]
  rw [hsum, hnum]

theorem ofPositiveWeights_mean_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (w : X → ℝ) (v : Y → ℝ) (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (htotal : 0 < ∑ x, w x) (vtotal : 0 < ∑ y, v y) (he : ∀ x, w x = v (e x))
    (f : X → ℝ) (g : Y → ℝ) (hfg : ∀ x, f x = g (e x)) :
    (ofPositiveWeights w hw htotal).mean f = (ofPositiveWeights v hv vtotal).mean g := by
  have h := congrArg Complex.re (ofPositiveWeights_complexMean_equiv e w v hw hv htotal vtotal he
    (fun x => (f x : ℂ)) (fun y => (g y : ℂ)) (fun x => congrArg Complex.ofReal (hfg x)))
  simpa only [complexMean_re, Complex.ofReal_re] using h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

def finiteEmbeddingRange {X Y : Type*} [Fintype Y] (e : Y ↪ X) : Finset X := Finset.univ.map e

theorem sum_finiteEmbeddingRange {X Y A : Type*} [Fintype Y] [AddCommMonoid A]
    (e : Y ↪ X) (f : X → A) : (∑ x ∈ finiteEmbeddingRange e, f x) = ∑ y, f (e y) := by
  rw [finiteEmbeddingRange, Finset.sum_map]

noncomputable def finiteEmbeddingRangeEquiv {X Y : Type*} [Fintype Y] (e : Y ↪ X) :
    Y ≃ ↥(finiteEmbeddingRange e) := Equiv.ofBijective
  (fun y => ⟨e y, Finset.mem_map.mpr ⟨y, Finset.mem_univ y, rfl⟩⟩) (by
    constructor
    · intro y z h
      exact e.injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨y, _, hy⟩ := Finset.mem_map.mp x.property
      exact ⟨y, Subtype.ext hy⟩)

namespace FiniteProbabilityWeights

theorem total_pos_of_embedding {X Y : Type*} [Fintype X] [Fintype Y]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (e : Y ↪ X) (h : 0 < ∑ y, w (e y)) : 0 < ∑ x, w x := by
  have hs : 0 < ∑ x ∈ finiteEmbeddingRange e, w x := by rw [sum_finiteEmbeddingRange]; exact h
  exact hs.trans_le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun x _ _ => hw x))

theorem conditionPositiveWeights_complexMean {X : Type*} [Fintype X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x)
    (G : Finset X) (hG : 0 < ∑ x ∈ G, w x) (f : X → ℂ) :
    (conditionPositiveWeights w hw hmass G hG).complexMean f =
      (∑ x ∈ G, (w x : ℂ) * f x) / ((∑ x ∈ G, w x : ℝ) : ℂ) := by
  simp only [complexMean, conditionPositiveWeights_weight, Complex.ofReal_div,
    div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  simp [restrictedWeight, apply_ite, ite_mul]

noncomputable def conditionAlongEmbedding {X Y : Type*} [Fintype X] [Fintype Y]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (e : Y ↪ X) (h : 0 < ∑ y, w (e y)) :
    FiniteProbabilityWeights X :=
  conditionPositiveWeights w hw (total_pos_of_embedding w hw e h) (finiteEmbeddingRange e)
    (by rw [sum_finiteEmbeddingRange]; exact h)

theorem conditionAlongEmbedding_complexMean {X Y : Type*} [Fintype X] [Fintype Y]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (e : Y ↪ X) (h : 0 < ∑ y, w (e y)) (f : X → ℂ) :
    (conditionAlongEmbedding w hw e h).complexMean f =
      (ofPositiveWeights (fun y => w (e y)) (fun y => hw (e y)) h).complexMean (fun y => f (e y)) := by
  rw [conditionAlongEmbedding, conditionPositiveWeights_complexMean, ofPositiveWeights_complexMean,
    sum_finiteEmbeddingRange, sum_finiteEmbeddingRange]

theorem conditionAlongEmbedding_mean {X Y : Type*} [Fintype X] [Fintype Y]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (e : Y ↪ X) (h : 0 < ∑ y, w (e y)) (f : X → ℝ) :
    (conditionAlongEmbedding w hw e h).mean f =
      (ofPositiveWeights (fun y => w (e y)) (fun y => hw (e y)) h).mean (fun y => f (e y)) := by
  have he := congrArg Complex.re (conditionAlongEmbedding_complexMean w hw e h (fun x => (f x : ℂ)))
  simpa only [complexMean_re, Complex.ofReal_re] using he

theorem uniform_condition_embedding_mean {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [Nonempty X]
    (e : Y ↪ X) (h : 0 < (uniform X).mass (finiteEmbeddingRange e)) (f : X → ℝ) :
    ((uniform X).condition (finiteEmbeddingRange e) h).mean f = 𝔼 y, f (e y) := by
  rw [uniform_condition_mean]
  exact (Fintype.expect_equiv (finiteEmbeddingRangeEquiv e) (fun y => f (e y)) (fun x => f x.val)
    (fun _ => rfl)).symm

end FiniteProbabilityWeights

end Erdos3

end

end OAI
