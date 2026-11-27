import GRHArticle.ProgressionFree.ExplicitArithmetic
import GRHArticle.ProgressionFree.RankinTruncation
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The marker-coordinate mass bound for the four-marker exchange

The admissible exponents below 27 give the first three ternary factors.
The remaining terms are bounded by an unrestricted geometric tail.
-/

namespace GRHArticle.ProgressionFree

open scoped BigOperators

private def exponentHead : Finset ℕ := {0, 1, 3, 4, 9, 10, 12, 13}

private theorem headDigitsTable : ∀ a ∈ Finset.range 27,
    (∀ d ∈ Nat.digits 3 a, d ≤ 1) ↔ a ∈ exponentHead := by
  decide +kernel

private theorem greedyExponentsBelow_twentySeven : greedyExponentsBelow 27 = exponentHead := by
  ext a
  rw [mem_greedyExponentsBelow]
  by_cases ha : a < 27
  · rw [and_iff_left ha]
    exact headDigitsTable a (Finset.mem_range.mpr ha)
  · have hhead : ∀ a ∈ exponentHead, a < 27 := by decide +kernel
    exact iff_of_false (fun h => ha h.2) (fun h => ha (hhead a h))

private theorem exponentHead_mass :
    (∑ a ∈ greedyExponentsBelow 27, (1 / (2 : ℝ)) ^ a) =
      (explicitUpsilon : ℝ) - (1 / (2 : ℝ)) ^ 26 := by
  rw [greedyExponentsBelow_twentySeven]
  norm_num [exponentHead, explicitUpsilon, Finset.sum_insert]

private theorem exponentTail_mass_le (S : Finset ℕ) (hS : ∀ a ∈ S, 27 ≤ a) :
    (∑ a ∈ S, (1 / (2 : ℝ)) ^ a) ≤ (1 / (2 : ℝ)) ^ 26 := by
  let r : ℝ := 1 / 2
  let f (a : ℕ) : ℝ := r ^ (a + 27)
  have hf : Summable f := by
    simpa only [f, pow_add] using
      (summable_geometric_of_lt_one (r := r) (by norm_num [r]) (by norm_num [r])).mul_right
        (r ^ 27)
  have hsum : (∑' a, f a) = r ^ 26 := by
    simp only [f, pow_add, tsum_mul_right,
      tsum_geometric_of_lt_one (r := r) (by norm_num [r]) (by norm_num [r])]
    norm_num [r]
  change (∑ a ∈ S, r ^ a) ≤ r ^ 26
  calc
    _ = ∑ a ∈ S, f (a - 27) := by
      apply Finset.sum_congr rfl
      intro a ha
      change r ^ a = r ^ (a - 27 + 27)
      rw [Nat.sub_add_cancel (hS a ha)]
    _ = ∑ a ∈ S.image (fun a => a - 27), f a := by
      symm
      apply Finset.sum_image
      intro a ha b hb hab
      have ha' := hS a ha
      have hb' := hS b hb
      change a - 27 = b - 27 at hab
      omega
    _ ≤ ∑' a, f a := hf.sum_le_tsum _ fun a _ => pow_nonneg (by norm_num [r]) _
    _ = _ := hsum

/-- Every finite admissible marker-coordinate mass is at most the explicit
dyadic quantity used in the gain calculation. -/
theorem greedyExponentsBelow_half_mass_le_upsilon (L : ℕ) :
    (∑ a ∈ greedyExponentsBelow L, (1 / (2 : ℝ)) ^ a) ≤ (explicitUpsilon : ℝ) := by
  let S := greedyExponentsBelow L
  let f (a : ℕ) : ℝ := (1 / (2 : ℝ)) ^ a
  have hsub : S.filter (· < 27) ⊆ greedyExponentsBelow 27 := by
    intro a ha
    have h := Finset.mem_filter.mp ha
    exact mem_greedyExponentsBelow.mpr ⟨(mem_greedyExponentsBelow.mp h.1).1, h.2⟩
  have hhead : (∑ a ∈ S.filter (· < 27), f a) ≤
      (explicitUpsilon : ℝ) - (1 / (2 : ℝ)) ^ 26 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by unfold f; positivity)).trans_eq
      exponentHead_mass
  have htail : (∑ a ∈ S.filter (fun a => ¬a < 27), f a) ≤ (1 / (2 : ℝ)) ^ 26 :=
    exponentTail_mass_le _ (fun _ ha => Nat.le_of_not_gt (Finset.mem_filter.mp ha).2)
  change (∑ a ∈ S, f a) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S (· < 27) f]
  linarith only [hhead, htail]

end GRHArticle.ProgressionFree
