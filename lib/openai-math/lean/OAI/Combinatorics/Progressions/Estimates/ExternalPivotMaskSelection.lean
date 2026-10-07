/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Sampling.ExternalNetMaskedScores
import OAI.Combinatorics.Progressions.Sampling.FiniteWeightedScorePerturbation

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem sum_externalNet_masked_complex_scores
    {J X Y I : Type*} [Fintype J] [Fintype I]
    (p : FiniteProbabilityWeights J) (idx : X → I)
    (physical : J → X) (point : J → Y) (w : X → ℂ) (centers : I → Y → ℂ) :
    (∑ i, p.complexMean (fun j =>
      (if idx (physical j) = i then w (physical j) else 0) * centers i (point j))) =
    p.complexMean (fun j => w (physical j) * centers (idx (physical j)) (point j)) := by
  simp only [FiniteProbabilityWeights.complexMean]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  simp only [ite_mul, zero_mul]
  simp

theorem exists_externalNet_large_masked_complex_score
    {J X Y I : Type*} [Fintype J] [Fintype I] [Nonempty I]
    (p : FiniteProbabilityWeights J) (F : X → Y → ℂ) (centers : I → Y → ℂ)
    {B ε δ : ℝ} (hnet : ∀ x, ∃ i, ∀ y, ‖F x y - centers i y‖ ≤ ε)
    (physical : J → X) (point : J → Y) (w : X → ℂ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hw : ∀ j, ‖w (physical j)‖ ≤ B)
    (hscore : δ ≤ ‖p.complexMean (fun j => w (physical j) * F (physical j) (point j))‖) :
    ∃ i, δ / (2 * Fintype.card I) ≤ ‖p.complexMean (fun j =>
      (if externalNetIndex F centers hnet (physical j) = i then w (physical j) else 0) *
        centers i (point j))‖ := by
  let idx := externalNetIndex F centers hnet
  let scores := fun i => p.complexMean (fun j =>
    (if idx (physical j) = i then w (physical j) else 0) * centers i (point j))
  have hnear := p.norm_complexMean_weighted_lower_of_perturbation
    (fun j => w (physical j)) (fun j => centers (idx (physical j)) (point j))
    (fun j => F (physical j) (point j)) hB hw
    (fun j => by rw [norm_sub_rev]; exact externalNetIndex_approx F centers hnet _ _) hscore
  have hsum : δ / 2 ≤ ‖∑ i, (1 : ℂ) * scores i‖ := by
    simp only [one_mul]
    rw [show (∑ i, scores i) = p.complexMean (fun j =>
      w (physical j) * centers (idx (physical j)) (point j)) from
        sum_externalNet_masked_complex_scores p idx physical point w centers]
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun _ : I => (1 : ℂ)) scores
    (by positivity : 0 < δ / 2) (show 0 < (Fintype.card I : ℝ) from Nat.cast_pos.mpr Fintype.card_pos)
    (by simp) hsum
  refine ⟨i, ?_⟩
  simpa only [scores, idx, div_div] using hi

theorem exists_simultaneous_external_pivot_masks
    {Ω J K X Y I : Type*} [Fintype Ω] [Fintype J] [Fintype K]
    [Fintype I] [Nonempty I]
    (F : K → X → Y → ℂ) (centers : K → I → Y → ℂ)
    {B ε δ : ℝ} (hnet : ∀ k x, ∃ i, ∀ y, ‖F k x y - centers k i y‖ ≤ ε)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → K → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → K → J → Y) (w : X → ℂ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hw : ∀ x, ‖w x‖ ≤ B)
    (hscore : ∀ a ∈ H, ∀ k, δ ≤ ‖(localLaw a k).complexMean
      (fun j => w (physical a j) * F k (physical a j) (point a k j))‖) :
    ∃ (chosen : K → I) (masked : K → X → ℂ) (H' : Finset Ω),
      (∀ k x, masked k x =
        if externalNetIndex (F k) (centers k) (hnet k) x = chosen k then w x else 0) ∧
      (∀ k x, ‖masked k x‖ ≤ B) ∧
      H' ⊆ H ∧ 0 < outer.mass H' ∧
      outer.mass H / (Fintype.card I : ℝ) ^ Fintype.card K ≤ outer.mass H' ∧
      ∀ a ∈ H', ∀ k, δ / (2 * Fintype.card I) ≤
        ‖(localLaw a k).complexMean (fun j => masked k (physical a j) *
          centers k (chosen k) (point a k j))‖ := by
  have hex (a : Ω) (ha : a ∈ H) (k : K) :=
    exists_externalNet_large_masked_complex_score (localLaw a k) (F k) (centers k)
      (hnet k) (physical a) (point a k) w hB hδ herror
      (fun j => hw _) (hscore a ha k)
  let code : Ω → K → I := fun a k =>
    if ha : a ∈ H then Classical.choose (hex a ha k) else Classical.choice inferInstance
  obtain ⟨chosen, hmass⟩ := outer.exists_code_fiber_mass H code
  let H' := H.filter (fun a => code a = chosen)
  have hsub : H' ⊆ H := Finset.filter_subset _ _
  have hmass' : outer.mass H / (Fintype.card I : ℝ) ^ Fintype.card K ≤ outer.mass H' := by
    rw [Fintype.card_fun, Nat.cast_pow] at hmass
    convert hmass using 1
    congr 1
    ext a
    simp only [H', Finset.mem_filter]
  have hpos : 0 < outer.mass H' :=
    (div_pos hH (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)).trans_le hmass'
  let masked := fun k x =>
    if externalNetIndex (F k) (centers k) (hnet k) x = chosen k then w x else 0
  refine ⟨chosen, masked, H', fun _ _ => rfl, ?_, hsub, hpos, hmass', ?_⟩
  · intro k x
    dsimp only [masked]
    split_ifs
    · exact hw x
    · simpa only [norm_zero] using hB
  · intro a ha k
    have hcode : code a = chosen := (Finset.mem_filter.mp ha).2
    have he := Classical.choose_spec (hex a (hsub ha) k)
    have hc : code a k = Classical.choose (hex a (hsub ha) k) := by
      simp only [code, dite_eq_left (hsub ha)]
    rw [← hc, hcode] at he
    exact he

end Erdos3

end

end OAI
