import OAI.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_fixed_two_shift_branches {K : Type*} [Fintype K] {N : ℕ} [NeZero N]
    (H : Finset (ZMod N)) (hH : H.Nonempty) (h0 : ZMod N)
    (f : ZMod N → K → ℤ → ℂ) (R : K → ℤ → ℂ) {rho : ℝ} (hrho : 0 < rho)
    (hf : ∀ h ∈ H, ∀ k n, ‖f h k n‖ ≤ 1) (hR : ∀ k n, ‖R k n‖ ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ k, rho ≤ ‖𝔼 x : ZMod N,
      f h k x.val * R k ((x + h).val : ℤ) * star (R k ((x + h0).val : ℤ))‖) :
    ∃ (branches : K → Bool × Bool) (S : Finset (ZMod N)), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-Real.log 4 * Fintype.card K) * H.card ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ k, ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧
        2 * ((len : ℤ) - 1) < N ∧
        rho / 20 ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
          f h k n * R k (n + cyclicBranchOffset h (branches k).1) *
            star (R k (n + cyclicBranchOffset h0 (branches k).2))‖ ∧
        rho / 20 ≤ (len : ℝ) / N := by
  let rel : ZMod N → K → Bool × Bool → Prop := fun h k b =>
    ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      rho / 20 ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        f h k n * R k (n + cyclicBranchOffset h b.1) * star (R k (n + cyclicBranchOffset h0 b.2))‖ ∧
      rho / 20 ≤ (len : ℝ) / N
  apply exists_large_fixed_choices H hH rel
  · intro h hh k
    obtain ⟨b, b0, a, len, hlen, hbound, hshort, hbias, hvol⟩ :=
      exists_two_shift_integer_interval (f h k) (R k) h h0 hrho (hf h hh k) (hR k) (hcorr h hh k)
    exact ⟨(b, b0), a, len, hlen, hbound, hshort, hbias, hvol⟩
  · rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num [Fintype.card_prod]

end Erdos3

end

end OAI
