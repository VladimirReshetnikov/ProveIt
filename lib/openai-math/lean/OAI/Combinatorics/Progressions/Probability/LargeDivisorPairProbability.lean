import OAI.Combinatorics.Progressions.Geometry.BoxPairDivisibility

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integer_box_pair_large_divisor_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (B R : ℕ) (hB : 0 < B) (hdim : 2 ≤ Fintype.card J)
    {L : ℝ} (hL : 0 < L) (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => ∃ m ∈ Finset.Ioc B R, ∀ j, (m : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      2 ^ (Fintype.card J - 1) *
        (1 / (B : ℝ) ^ (Fintype.card J - 1) + (R : ℝ) / L ^ Fintype.card J) := by
  let p := (integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)
  have hunion := p.eventProbability_union_bound
    (fun xy => ∃ m ∈ Finset.Ioc B R, ∀ j, (m : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ))
    (fun (m : Finset.Ioc B R) xy => ∀ j, (m.val : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ))
    (by intro xy h; obtain ⟨m, hm, hd⟩ := h; exact ⟨⟨m, hm⟩, hd⟩)
  have hsum : p.eventProbability
      (fun xy => ∃ m ∈ Finset.Ioc B R, ∀ j, (m : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      ∑ m ∈ Finset.Ioc B R, (1 / (m : ℝ) + 1 / L) ^ Fintype.card J := by
    apply hunion.trans
    calc
      _ ≤ ∑ m : Finset.Ioc B R, (1 / (m.val : ℝ) + 1 / L) ^ Fintype.card J := by
        apply Finset.sum_le_sum
        intro m _
        have hm : 0 < m.val := hB.trans (Finset.mem_Ioc.mp m.property).1
        simpa only [p, Int.cast_natCast] using integer_box_pair_divisor_probability_of_lengths lo hi hlen
          (m.val : ℤ) (by exact_mod_cast hm) hL hside
      _ = _ := Finset.sum_coe_sort (Finset.Ioc B R)
        (fun m : ℕ => (1 / (m : ℝ) + 1 / L) ^ Fintype.card J)
  have htail := finite_divisor_error_tail (Finset.Ioc B R) hB hdim
    (fun m hm => (Finset.mem_Ioc.mp hm).1) hL
  have hcard : ((Finset.Ioc B R).card : ℝ) ≤ R := by
    exact_mod_cast (show (Finset.Ioc B R).card ≤ R by simp)
  apply hsum.trans (htail.trans _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (div_le_div_of_nonneg_right hcard (by positivity))

theorem nonzero_common_divisor_bounded {J : Type*} (z : J → ℤ) (hz : z ≠ 0)
    {R m : ℕ} (hR : ∀ j, (z j).natAbs ≤ R) (hdiv : ∀ j, (m : ℤ) ∣ z j) : m ≤ R := by
  obtain ⟨j, hj⟩ : ∃ j, z j ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  have h := (Int.natAbs_le_of_dvd_ne_zero (hdiv j) hj).trans (hR j)
  simpa using h

theorem integer_box_pair_nonzero_large_divisor_probability {J : Type*}
    [Fintype J] [DecidableEq J] (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (B R : ℕ) (hB : 0 < B) (hdim : 2 ≤ Fintype.card J)
    {L : ℝ} (hL : 0 < L) (hside : ∀ j, L ≤ ((hi j - lo j : ℤ) : ℝ))
    (hwidth : ∀ j, hi j - lo j ≤ (R : ℤ)) :
    ((integerBoxUniformWeights lo hi hlen).prod (integerBoxUniformWeights lo hi hlen)).eventProbability
        (fun xy => xy.1 ≠ xy.2 ∧
          ∃ m : ℕ, B < m ∧ ∀ j, (m : ℤ) ∣ (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≤
      2 ^ (Fintype.card J - 1) *
        (1 / (B : ℝ) ^ (Fintype.card J - 1) + (R : ℝ) / L ^ Fintype.card J) := by
  apply (FiniteProbabilityWeights.eventProbability_mono _ _ _ ?_).trans
    (integer_box_pair_large_divisor_probability lo hi hlen B R hB hdim hL hside)
  intro xy hxy
  obtain ⟨hne, m, hm, hd⟩ := hxy
  have hz : (fun j => (xy.2 j : ℤ) - (xy.1 j : ℤ)) ≠ 0 := by
    intro he
    apply hne
    funext j
    apply Subtype.ext
    have hj := congrFun he j
    change (xy.2 j : ℤ) - (xy.1 j : ℤ) = 0 at hj
    omega
  have hR : ∀ j, ((xy.2 j : ℤ) - (xy.1 j : ℤ)).natAbs ≤ R := by
    intro j
    have hx := Finset.mem_Ico.mp (xy.1 j).property
    have hy := Finset.mem_Ico.mp (xy.2 j).property
    have hw := hwidth j
    have habs : |(xy.2 j : ℤ) - (xy.1 j : ℤ)| ≤ (R : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
    have hc : (((xy.2 j : ℤ) - (xy.1 j : ℤ)).natAbs : ℤ) ≤ R := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hc
  exact ⟨m, Finset.mem_Ioc.mpr ⟨hm, nonzero_common_divisor_bounded _ hz hR hd⟩, hd⟩

end Erdos3

end

end OAI
