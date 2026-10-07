import OAI.Combinatorics.Progressions.Estimates.ScalarDominatedSlack

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem exists_partition_score_retention {Ω I : Type*} [Fintype Ω] [Fintype I]
    [Nonempty I] (outer : FiniteProbabilityWeights Ω) (H : Finset Ω)
    (hH : 0 < outer.mass H) (scores : Ω → I → ℝ) (t : ℝ) (_ht : 0 < t)
    (hscores : ∀ a ∈ H, t ≤ ∑ i, scores a i) :
    ∃ (i : I) (H' : Finset Ω), H' ⊆ H ∧ 0 < outer.mass H' ∧
      outer.mass H / Fintype.card I ≤ outer.mass H' ∧
      ∀ a ∈ H', t / Fintype.card I ≤ scores a i := by
  classical
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hex : ∀ a, ∃ i, a ∈ H → t / Fintype.card I ≤ scores a i := by
    intro a
    by_cases ha : a ∈ H
    · have hmean : t / Fintype.card I ≤ 𝔼 i, scores a i := by
        rw [Fintype.expect_eq_sum_div_card]
        exact div_le_div_of_nonneg_right (hscores a ha) hcard.le
      obtain ⟨i, _, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
      exact ⟨i, fun _ => hi⟩
    · exact ⟨Classical.choice inferInstance, fun h => (ha h).elim⟩
  choose code hcode using hex
  obtain ⟨i, hi⟩ := outer.exists_code_fiber_mass H code
  refine ⟨i, H.filter (fun a => code a = i), Finset.filter_subset _ _,
    lt_of_lt_of_le (div_pos hH hcard) hi, hi, ?_⟩
  intro a ha
  obtain ⟨haH, hai⟩ := Finset.mem_filter.mp ha
  simpa only [hai] using hcode a haH

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def externalNetIndex {X Y I : Type*}
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) : X → I :=
  fun x => Classical.choose (hnet x)

theorem externalNetIndex_approx {X Y I : Type*}
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε) (x : X) (y : Y) :
    ‖F x y - centers (externalNetIndex F centers hnet x) y‖ ≤ ε :=
  Classical.choose_spec (hnet x) y

theorem sum_externalNet_masked_scores {G X Y I : Type*} [Fintype G] [Fintype I]
    (p : FiniteProbabilityWeights G) (idx : X → I)
    (physical : G → X) (lowerPoint : G → Y) (w : G → ℝ)
    (centers : I → Y → ℂ) :
    (∑ i, p.mean (fun z =>
      (if idx (physical z) = i then w z else 0) * (centers i (lowerPoint z)).re)) =
    p.mean (fun z => w z * (centers (idx (physical z)) (lowerPoint z)).re) := by
  classical
  rw [← p.mean_sum]
  congr 1
  funext z
  simp only [ite_mul, zero_mul]
  simp

theorem externalNet_selected_score_lower {G X Y I : Type*} [Fintype G]
    (p : FiniteProbabilityWeights G) (F : X → Y → ℂ)
    (centers : I → Y → ℂ) (idx : X → I)
    (physical : G → X) (lowerPoint : G → Y) (w : G → ℝ)
    {B ε δ : ℝ} (hB : 0 ≤ B) (hw : ∀ z, |w z| ≤ B)
    (happrox : ∀ x y, ‖F x y - centers (idx x) y‖ ≤ ε)
    (hscore : δ ≤ p.mean (fun z => w z * (F (physical z) (lowerPoint z)).re)) :
    δ - B * ε ≤ p.mean
      (fun z => w z * (centers (idx (physical z)) (lowerPoint z)).re) := by
  have hpoint (z : G) :
      w z * (F (physical z) (lowerPoint z)).re -
        w z * (centers (idx (physical z)) (lowerPoint z)).re ≤ B * ε := by
    rw [← mul_sub]
    calc
      _ ≤ |w z * ((F (physical z) (lowerPoint z)).re -
          (centers (idx (physical z)) (lowerPoint z)).re)| := le_abs_self _
      _ = |w z| * |(F (physical z) (lowerPoint z) -
          centers (idx (physical z)) (lowerPoint z)).re| := by rw [abs_mul]; rfl
      _ ≤ B * ε := mul_le_mul (hw z)
        ((Complex.abs_re_le_norm _).trans (happrox _ _)) (abs_nonneg _) hB
  have hmean := p.mean_mono hpoint
  rw [p.mean_sub, p.mean_const] at hmean
  linarith

theorem externalNetIndex_retained_masked_scores
    {Ω G X Y I : Type*} [Fintype Ω] [Fintype G] [Fintype I] [Nonempty I]
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {B ε δ : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights G)
    (physical : Ω → G → X) (lowerPoint : Ω → G → Y) (w : Ω → G → ℝ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hw : ∀ a ∈ H, ∀ z, |w a z| ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ (localLaw a).mean
      (fun z => w a z * (F (physical a z) (lowerPoint a z)).re)) :
    ∃ (i : I) (H' : Finset Ω), H' ⊆ H ∧ 0 < outer.mass H' ∧
      outer.mass H / Fintype.card I ≤ outer.mass H' ∧
      ∀ a ∈ H', δ / (2 * Fintype.card I) ≤ (localLaw a).mean (fun z =>
        (if externalNetIndex F centers hnet (physical a z) = i then w a z else 0) *
          (centers i (lowerPoint a z)).re) := by
  let idx := externalNetIndex F centers hnet
  let scores := fun a i => (localLaw a).mean (fun z =>
    (if idx (physical a z) = i then w a z else 0) * (centers i (lowerPoint a z)).re)
  have htotal : ∀ a ∈ H, δ / 2 ≤ ∑ i, scores a i := by
    intro a ha
    dsimp only [scores]
    rw [sum_externalNet_masked_scores]
    have h := externalNet_selected_score_lower (localLaw a) F centers idx
      (physical a) (lowerPoint a) (w a) hB (hw a ha)
      (externalNetIndex_approx F centers hnet) (hscore a ha)
    linarith
  obtain ⟨i, H', hsub, hpos, hmass, hretained⟩ :=
    outer.exists_partition_score_retention H hH scores (δ / 2) (by positivity) htotal
  refine ⟨i, H', hsub, hpos, hmass, ?_⟩
  intro a ha
  simpa only [scores, idx, div_div] using hretained a ha

theorem exists_externalNet_common_mask
    {Ω G X Y I : Type*} [Fintype Ω] [Fintype G] [Fintype I] [Nonempty I]
    (F : X → Y → ℂ) (centers : I → Y → ℂ) {B ε δ : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights G)
    (physical : Ω → G → X) (lowerPoint : Ω → G → Y) (w : X → ℝ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hw : ∀ x, |w x| ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ (localLaw a).mean
      (fun z => w (physical a z) * (F (physical a z) (lowerPoint a z)).re)) :
    ∃ (i : I) (masked : X → ℝ) (H' : Finset Ω),
      (∀ x, masked x = if externalNetIndex F centers hnet x = i then w x else 0) ∧
      (∀ x, |masked x| ≤ B) ∧
      H' ⊆ H ∧ 0 < outer.mass H' ∧
      outer.mass H / Fintype.card I ≤ outer.mass H' ∧
      ∀ a ∈ H', δ / (2 * Fintype.card I) ≤ (localLaw a).mean
        (fun z => masked (physical a z) * (centers i (lowerPoint a z)).re) := by
  obtain ⟨i, H', hsub, hpos, hmass, hretained⟩ :=
    externalNetIndex_retained_masked_scores F centers hnet outer H hH localLaw
      physical lowerPoint (fun a z => w (physical a z)) hB hδ herror
      (fun _ _ z => hw _) hscore
  refine ⟨i, (fun x => if externalNetIndex F centers hnet x = i then w x else 0),
    H', (fun _ => rfl), ?_, hsub, hpos, hmass, hretained⟩
  intro x
  dsimp only
  split_ifs
  · exact hw x
  · simpa only [abs_zero] using hB

end Erdos3

end

end OAI
