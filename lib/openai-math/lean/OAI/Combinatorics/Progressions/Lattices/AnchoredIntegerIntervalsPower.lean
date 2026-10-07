import OAI.Combinatorics.Progressions.Dynamics.AnchorLossBudget
import OAI.Combinatorics.Progressions.Estimates.FixedTwoShiftBranches

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_anchored_integer_intervals {K : Type*} [Fintype K] {N : ℕ} [NeZero N]
    (H : Finset (ZMod N)) (hH : H.Nonempty)
    (U : ZMod N → K → ℤ → ℂ) (Q R : K → ℤ → ℂ) {delta : ℝ} (hdelta : 0 < delta)
    (hU : ∀ h ∈ H, ∀ k n, ‖U h k n‖ ≤ 1)
    (hQ : ∀ k n, ‖Q k n‖ ≤ 1) (hR : ∀ k n, ‖R k n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 x : ZMod N,
      U h k x.val * Q k x.val * R k ((x + h).val : ℤ)‖) :
    ∃ h0 ∈ H, ∃ (branches : K → Bool × Bool) (S : Finset (ZMod N)),
      S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-Real.log 4 * Fintype.card K) * (delta ^ (2 * Fintype.card K) / 2) * H.card ≤
        (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧
        2 * ((len : ℤ) - 1) < N ∧
        delta ^ (2 * Fintype.card K) / 40 ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            partnerAnchorWeight (U h k) (U h0 k) (Q k) n *
              R k (n + cyclicBranchOffset h (branches k).1) *
              star (R k (n + cyclicBranchOffset h0 (branches k).2))‖ ∧
        delta ^ (2 * Fintype.card K) / 40 ≤ (len : ℝ) / N := by
  obtain ⟨h0, hh0, H', hsub, hH'n, hsize, hanchor⟩ := exists_fixed_partner_anchor H hH
    (fun h k x => U h k x.val) (fun k x => Q k x.val) (fun k x => R k x.val) hdelta
    (fun h hh k x => hU h hh k x.val) (fun k x => hQ k x.val) (fun k x => hR k x.val) hcorr
  let f : ZMod N → K → ℤ → ℂ := fun h k => partnerAnchorWeight (U h k) (U h0 k) (Q k)
  have hf : ∀ h ∈ H', ∀ k n, ‖f h k n‖ ≤ 1 := by
    intro h hh k n
    exact partnerAnchorWeight_norm_le_one (U h k) (U h0 k) (Q k)
      (hU h (hsub hh) k) (hU h0 hh0 k) (hQ k) n
  have hcorr' : ∀ h ∈ H', ∀ k, delta ^ (2 * Fintype.card K) / 2 ≤
      ‖𝔼 x : ZMod N, f h k x.val * R k ((x + h).val : ℤ) * star (R k ((x + h0).val : ℤ))‖ :=
    hanchor
  obtain ⟨branches, S, hSH', hSn, hcard, hinterval⟩ := exists_fixed_two_shift_branches
    H' hH'n h0 f R (by positivity) hf hR hcorr'
  refine ⟨h0, hh0, branches, S, fun h hh => hsub (hSH' hh), hSn, ?_, ?_⟩
  · calc
      _ = Real.exp (-Real.log 4 * Fintype.card K) *
          ((delta ^ (2 * Fintype.card K) / 2) * H.card) := mul_assoc _ _ _
      _ ≤ Real.exp (-Real.log 4 * Fintype.card K) * H'.card :=
        mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le
      _ ≤ _ := hcard
  · intro h hh k
    obtain ⟨a, len, hlen, hbound, hshort, hbias, hvol⟩ := hinterval h hh k
    refine ⟨a, len, hlen, hbound, hshort, ?_, ?_⟩
    · simpa only [div_div, show (2 : ℝ) * 20 = 40 by norm_num] using hbias
    · simpa only [div_div, show (2 : ℝ) * 20 = 40 by norm_num] using hvol

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_anchored_integer_intervals_power {K : Type*} [Fintype K] {N : ℕ} [NeZero N]
    (H : Finset (ZMod N)) (U : ZMod N → K → ℤ → ℂ) (Q R : K → ℤ → ℂ)
    {p delta : ℝ} (hp : 2 ≤ p) (hm : (Fintype.card K : ℝ) ≤ p)
    (hdelta : Real.exp (-p) ≤ delta) (hH : Real.exp (-p) * N ≤ (H.card : ℝ))
    (hU : ∀ h ∈ H, ∀ k n, ‖U h k n‖ ≤ 1)
    (hQ : ∀ k n, ‖Q k n‖ ≤ 1) (hR : ∀ k n, ‖R k n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, delta ≤ ‖𝔼 x : ZMod N,
      U h k x.val * Q k x.val * R k ((x + h).val : ℤ)‖) :
    ∃ h0 ∈ H, ∃ (branches : K → Bool × Bool) (S : Finset (ZMod N)),
      S ⊆ H ∧ S.Nonempty ∧ Real.exp (-((p + 2) ^ 3)) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧
        2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-((p + 2) ^ 3)) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            partnerAnchorWeight (U h k) (U h0 k) (Q k) n *
              R k (n + cyclicBranchOffset h (branches k).1) *
              star (R k (n + cyclicBranchOffset h0 (branches k).2))‖ ∧
        Real.exp (-((p + 2) ^ 3)) ≤ (len : ℝ) / N := by
  have hdelta0 : 0 < delta := (Real.exp_pos _).trans_le hdelta
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hHpos : (0 : ℝ) < H.card := (mul_pos (Real.exp_pos _) hN).trans_le hH
  have hHn : H.Nonempty := Finset.card_pos.mp (by exact_mod_cast hHpos)
  obtain ⟨h0, hh0, branches, S, hsub, hSn, hsize, hinterval⟩ :=
    exists_anchored_integer_intervals H hHn U Q R hdelta0 hU hQ hR hcorr
  have hB : 0 ≤ Real.exp (-Real.log 4 * Fintype.card K) * (delta ^ (2 * Fintype.card K) / 2) :=
    mul_nonneg (Real.exp_nonneg _) (by positivity)
  refine ⟨h0, hh0, branches, S, hsub, hSn, ?_, ?_⟩
  · calc
      _ ≤ (Real.exp (-Real.log 4 * Fintype.card K) *
          (delta ^ (2 * Fintype.card K) / 2) * Real.exp (-p)) * N :=
        mul_le_mul_of_nonneg_right (anchored_density_budget hp hm hdelta le_rfl) hN.le
      _ = (Real.exp (-Real.log 4 * Fintype.card K) *
          (delta ^ (2 * Fintype.card K) / 2)) * (Real.exp (-p) * N) := by ring
      _ ≤ (Real.exp (-Real.log 4 * Fintype.card K) *
          (delta ^ (2 * Fintype.card K) / 2)) * H.card := mul_le_mul_of_nonneg_left hH hB
      _ ≤ _ := hsize
  · intro h hh k
    obtain ⟨a, len, hlen, hbound, hshort, hbias, hvol⟩ := hinterval h hh k
    exact ⟨a, len, hlen, hbound, hshort, (anchored_interval_budget hp hm hdelta).trans hbias,
      (anchored_interval_budget hp hm hdelta).trans hvol⟩

end Erdos3

end

end OAI
