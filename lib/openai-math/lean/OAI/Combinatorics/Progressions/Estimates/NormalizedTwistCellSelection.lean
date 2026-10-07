import OAI.Combinatorics.Progressions.Probability.PositiveDensityRetained

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

noncomputable def fiberComplexMean {X R : Type*} [Fintype X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (r : R) (f : X → ℂ) : ℂ :=
  p.complexMean (fun x => if F x = r then f x else 0)

theorem sum_fiberComplexMean_on {X R : Type*} [Fintype X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (S : Finset R) (f : X → ℂ) :
    (∑ r ∈ S, p.fiberComplexMean F r f) = p.complexMean (fun x => if F x ∈ S then f x else 0) := by
  unfold fiberComplexMean complexMean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  by_cases h : F x ∈ S <;> simp [eq_comm, h]

theorem mass_mul_condition_complexMean {X : Type*} [Fintype X] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (G : Finset X) (hG : 0 < p.mass G) (f : X → ℂ) :
    (p.mass G : ℂ) * (p.condition G hG).complexMean f =
      p.complexMean (fun x => if x ∈ G then f x else 0) := by
  have h := p.mass_mul_condition_correlation G hG f (fun _ => 1)
  simpa only [correlation, complexMean, finiteMask_apply, star_one, mul_one] using h

theorem fiberComplexMean_eq_condition {X R : Type*} [Fintype X] [DecidableEq X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (r : R) (f : X → ℂ)
    (hG : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) :
    p.fiberComplexMean F r f =
      (p.mass (Finset.univ.filter (fun x => F x = r)) : ℂ) *
        (p.condition (Finset.univ.filter (fun x => F x = r)) hG).complexMean f := by
  rw [p.mass_mul_condition_complexMean]
  simp only [fiberComplexMean, Finset.mem_filter, Finset.mem_univ, true_and]

theorem sum_condition_complexMean_on {X R : Type*} [Fintype X] [DecidableEq X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (S : Finset R)
    (hS : ∀ r ∈ S, 0 < p.mass (Finset.univ.filter (fun x => F x = r))) (f : X → ℂ) :
    (∑ r : S, (p.mass (Finset.univ.filter (fun x => F x = r.val)) : ℂ) *
      (p.condition (Finset.univ.filter (fun x => F x = r.val)) (hS r.val r.property)).complexMean f) =
        p.complexMean (fun x => if F x ∈ S then f x else 0) := by
  calc
    _ = ∑ r : S, p.fiberComplexMean F r.val f := by
      apply Finset.sum_congr rfl
      intro r _
      exact (p.fiberComplexMean_eq_condition F r.val f (hS r.val r.property)).symm
    _ = ∑ r ∈ S, p.fiberComplexMean F r f :=
      Finset.sum_coe_sort S (fun r => p.fiberComplexMean F r f)
    _ = _ := p.sum_fiberComplexMean_on F S f

theorem retained_condition_mixture_error {X R : Type*} [Fintype X] [DecidableEq X] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (S : Finset R)
    (hS : ∀ r ∈ S, 0 < p.mass (Finset.univ.filter (fun x => F x = r)))
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.complexMean f -
      ∑ r : S, (p.mass (Finset.univ.filter (fun x => F x = r.val)) : ℂ) *
        (p.condition (Finset.univ.filter (fun x => F x = r.val)) (hS r.val r.property)).complexMean f‖ ≤
      p.mass (Finset.univ.filter (fun x => F x ∉ S)) := by
  rw [p.sum_condition_complexMean_on F S hS f]
  have h := p.norm_complexMean_remove_set_le_mass (Finset.univ.filter (fun x => F x ∉ S)) f hf
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ite_not] using h

theorem sum_fiber_masses_le_one {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    (p : FiniteProbabilityWeights X) (F : X → R) (S : Finset R) :
    (∑ r : S, p.mass (Finset.univ.filter (fun x => F x = r.val))) ≤ 1 := by
  calc
    _ = ∑ r : S, (p.fiberLaw F).weight r.val := by
      apply Finset.sum_congr rfl
      intro r _
      rw [p.fiberLaw_weight_eq_mass]
    _ = (p.fiberLaw F).mass S := Finset.sum_coe_sort S (fun r => (p.fiberLaw F).weight r)
    _ ≤ 1 := (p.fiberLaw F).mass_le_one S

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem ofPositiveWeights_condition_embedding_complexMean {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : 0 < ∑ x, w x)
    (e : Y ↪ X) (hchild : 0 < ∑ y, w (e y))
    (hG : 0 < (ofPositiveWeights w hw htotal).mass (finiteEmbeddingRange e)) (f : X → ℂ) :
    ((ofPositiveWeights w hw htotal).condition (finiteEmbeddingRange e) hG).complexMean f =
      (ofPositiveWeights (fun y => w (e y)) (fun y => hw (e y)) hchild).complexMean
        (fun y => f (e y)) := by
  have hraw : 0 < ∑ x ∈ finiteEmbeddingRange e, w x := by
    rw [sum_finiteEmbeddingRange]
    exact hchild
  change (conditionPositiveWeights w hw htotal (finiteEmbeddingRange e) hraw).complexMean f = _
  rw [ofPositiveWeights_complexMean]
  have hratio : (conditionPositiveWeights w hw htotal (finiteEmbeddingRange e) hraw).complexMean f =
      (∑ x ∈ finiteEmbeddingRange e, (w x : ℂ) * f x) /
        ((∑ x ∈ finiteEmbeddingRange e, w x : ℝ) : ℂ) := by
    simp only [complexMean, conditionPositiveWeights_weight, Complex.ofReal_div,
      div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    simp [restrictedWeight, apply_ite, ite_mul]
  rw [hratio, sum_finiteEmbeddingRange, sum_finiteEmbeddingRange]

theorem ofPositiveWeights_embedded_fiber_complexMean {X Y R : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq R]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : 0 < ∑ x, w x)
    (F : X → R) (r : R) (e : Y ↪ X)
    (hcell : finiteEmbeddingRange e = Finset.univ.filter (fun x => F x = r))
    (hchild : 0 < ∑ y, w (e y)) (f : X → ℂ) :
    ((ofPositiveWeights w hw htotal).mass (Finset.univ.filter (fun x => F x = r)) : ℂ) *
      (ofPositiveWeights (fun y => w (e y)) (fun y => hw (e y)) hchild).complexMean
        (fun y => f (e y)) = (ofPositiveWeights w hw htotal).fiberComplexMean F r f := by
  have hG : 0 < (ofPositiveWeights w hw htotal).mass (finiteEmbeddingRange e) := by
    rw [ofPositiveWeights_mass, sum_finiteEmbeddingRange]
    exact div_pos hchild htotal
  rw [← ofPositiveWeights_condition_embedding_complexMean w hw htotal e hchild hG f,
    ← hcell, mass_mul_condition_complexMean]
  rw [hcell]
  simp only [fiberComplexMean, Finset.mem_filter, Finset.mem_univ, true_and]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X C : Type*} [Fintype X] [DecidableEq X]
  [Fintype C] [DecidableEq C] [Nonempty C]

theorem exists_large_correlating_fiber (p : FiniteProbabilityWeights X)
    (cell : X → C) (f : X → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hbias : δ ≤ ‖p.complexMean f‖) :
    ∃ (c : C) (hc : 0 < p.mass (Finset.univ.filter (fun x => cell x = c))),
      δ / (2 * Fintype.card C) ≤ p.mass (Finset.univ.filter (fun x => cell x = c)) ∧
      δ / 2 ≤ ‖(p.condition (Finset.univ.filter (fun x => cell x = c)) hc).complexMean f‖ := by
  let mass := fun c => p.mass (Finset.univ.filter (fun x => cell x = c))
  let term := fun c => p.fiberComplexMean cell c f
  have hmass : (∑ c, mass c) = 1 := by
    simpa only [mass, ← p.fiberLaw_weight_eq_mass cell] using (p.fiberLaw cell).total
  have hsum : (∑ c, term c) = p.complexMean f := by
    simpa only [term, Finset.mem_univ, ite_true] using
      p.sum_fiberComplexMean_on cell Finset.univ f
  have hcap (c : C) : ‖term c‖ ≤ mass c := by
    apply (p.norm_complexMean_le_mean_norm _).trans
    dsimp only [mass]
    rw [← p.mean_indicator (Finset.univ.filter (fun x => cell x = c))]
    apply p.mean_mono
    intro x
    by_cases hx : cell x = c
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hx, ite_true] using hf x
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx, ite_false, norm_zero, le_refl]
  have hcard : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hscore : δ / (2 * Fintype.card C) ≤
      𝔼 c, (‖term c‖ - δ / 2 * mass c) := by
    rw [Fintype.expect_eq_sum_div_card, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, mul_one]
    have hn := (norm_sum_le _ _).trans' (hsum.symm ▸ hbias)
    apply (le_div_iff₀ hcard).mpr
    have he : δ / (2 * Fintype.card C) * Fintype.card C = δ / 2 := by
      field_simp
    rw [he]
    linarith
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hscore
  have hsmall : 0 < δ / (2 * Fintype.card C) := div_pos hδ (by positivity)
  have hmass0 : 0 ≤ mass c := p.mass_nonneg _
  have hmasslower : δ / (2 * Fintype.card C) ≤ mass c := by
    nlinarith [hcap c]
  have hmasspos : 0 < mass c := hsmall.trans_le hmasslower
  refine ⟨c, hmasspos, hmasslower, ?_⟩
  have hid : ‖term c‖ = mass c *
      ‖(p.condition (Finset.univ.filter (fun x => cell x = c)) hmasspos).complexMean f‖ := by
    dsimp only [term]
    rw [p.fiberComplexMean_eq_condition cell c f hmasspos, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hmass0]
  rw [hid] at hc
  nlinarith

theorem exists_large_correlating_fiber_of_approximation (p : FiniteProbabilityWeights X)
    (cell : X → C) (f : X → ℂ) (g : C → X → ℂ) {δ ε : ℝ} (hδ : 0 < δ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hbias : δ ≤ ‖p.complexMean f‖)
    (happrox : ∀ c x, cell x = c → ‖f x - g c x‖ ≤ ε) :
    ∃ (c : C) (hc : 0 < p.mass (Finset.univ.filter (fun x => cell x = c))),
      δ / (2 * Fintype.card C) ≤ p.mass (Finset.univ.filter (fun x => cell x = c)) ∧
      δ / 2 - ε ≤
        ‖(p.condition (Finset.univ.filter (fun x => cell x = c)) hc).complexMean (g c)‖ := by
  obtain ⟨c, hc, hmass, hcorr⟩ := p.exists_large_correlating_fiber cell f hδ hf hbias
  refine ⟨c, hc, hmass, ?_⟩
  let q := p.condition (Finset.univ.filter (fun x => cell x = c)) hc
  have herr : ‖q.complexMean f - q.complexMean (g c)‖ ≤ ε := by
    apply (q.norm_complexMean_sub_le f (g c) (fun _ => ε) ?_).trans_eq (q.mean_const ε)
    intro x hx
    apply happrox c x
    by_contra hn
    have hz : q.weight x = 0 := by
      simp only [q, condition, Finset.mem_filter, Finset.mem_univ, true_and,
        hn, ite_false, zero_div]
    exact hx hz
  have htri := norm_le_norm_sub_add (q.complexMean f) (q.complexMean (g c))
  change δ / 2 ≤ ‖q.complexMean f‖ at hcorr
  change δ / 2 - ε ≤ ‖q.complexMean (g c)‖
  linarith

end Erdos3.FiniteProbabilityWeights

end

end OAI
