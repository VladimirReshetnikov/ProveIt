import GowersSzemeredi.Proofs16BohrSumUniformParameters

/-! One coefficient cutoff for a family of Bohr sets with bounded rank. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem polynomialSpectrumCutoff_mono_rank {m n : Nat} (hmn : m ≤ n)
    {rho epsilon : Real} (hrho : 0 < rho) (heps : 0 < epsilon) :
    polynomialSpectrumCutoff m rho epsilon ≤ polynomialSpectrumCutoff n rho epsilon := by
  unfold polynomialSpectrumCutoff
  apply Nat.ceil_mono
  have hmnR : (m : Real) ≤ n := by exact_mod_cast hmn
  apply max_le_max <;> gcongr

theorem bohrSumRankThreshold_antitone_ranks {k l r : Nat} (hk : k ≤ r) (hl : l ≤ r)
    (M : Nat) [NeZero M] : bohrSumRankThreshold r r M M ≤ bohrSumRankThreshold k l M M := by
  have hM : (1 : Real) ≤ M := by exact_mod_cast NeZero.pos M
  have hMk : (M : Real)^k ≤ (M : Real)^r := by gcongr
  have hMl : (M : Real)^l ≤ (M : Real)^r := by gcongr
  unfold bohrSumRankThreshold
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

/-- A common cutoff for two Bohr sets whose ranks are at most r. -/
theorem bohr_sum_contains_rank_cap_span {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) (r M : Nat) [NeZero M]
    (hK : K.card ≤ r) (hL : L.card ≤ r) {rho : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hM : 2 ≤ rho * M) (d : ZMod N)
    (hd : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N))
        (polynomialSpectrumCutoff r (rho / 2) (bohrSumRankThreshold r r M M)) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N))
        (polynomialSpectrumCutoff r (rho / 2) (bohrSumRankThreshold r r M M)))
      (1 / (4 * Real.pi))) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L rho, d = x + y := by
  have htpos := bohrSumRankThreshold_pos r r M M
  have ht := bohrSumRankThreshold_antitone_ranks hK hL M
  have hRK := (polynomialSpectrumCutoff_antitone K.card (half_pos hrho) htpos ht).trans
    (polynomialSpectrumCutoff_mono_rank hK (half_pos hrho) htpos)
  have hRL := (polynomialSpectrumCutoff_antitone L.card (half_pos hrho) htpos ht).trans
    (polynomialSpectrumCutoff_mono_rank hL (half_pos hrho) htpos)
  apply bohr_sum_contains_rank_controlled_span K L M M hrho hrho1 hrho hrho1 hM hM d
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q hq => ?_⟩
  obtain ⟨hqK, hqL⟩ := Finset.mem_inter.mp hq
  exact (Finset.mem_filter.mp hd).2 q (Finset.mem_inter.mpr
    ⟨boundedFrequencySpan_mono _ hRK hqK, boundedFrequencySpan_mono _ hRL hqL⟩)

end LeanProofs.GowersSzemeredi
