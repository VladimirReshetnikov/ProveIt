import GowersSzemeredi.Proofs16SpectrumPairSumset
import GowersSzemeredi.Proofs16BohrSumRankCap

/-! Quarter-radius Bohr-sum containment with uniform coefficient cutoffs.
The doubled Fourier threshold is valid at every prime modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The half-radius Bohr densities are at most one. -/
theorem bohrSumThreshold_le_quarter {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) (rho sigma : Real) :
    bohrSumThreshold K L rho sigma ≤ 1 / 4 := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hA : ((bohr K (rho / 2)).card : Real) ≤ N := by
    exact_mod_cast (show (bohr K (rho / 2)).card ≤ N by simpa using Finset.card_le_univ (bohr K (rho / 2)))
  have hB : ((bohr L (sigma / 2)).card : Real) ≤ N := by
    exact_mod_cast (show (bohr L (sigma / 2)).card ≤ N by simpa using Finset.card_le_univ (bohr L (sigma / 2)))
  have hprod := mul_le_mul hA hB (Nat.cast_nonneg _) hN.le
  unfold bohrSumThreshold
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hprod]

/-- Bohr-sum containment without a lower bound on the modulus. -/
theorem bohr_sum_contains_span_intersection_uniform_quarter {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) {rho sigma : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (d : ZMod N)
    (hd : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N))
        (polynomialSpectrumCutoff K.card (rho / 2) (2 * bohrSumThreshold K L rho sigma)) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N))
        (polynomialSpectrumCutoff L.card (sigma / 2) (2 * bohrSumThreshold K L rho sigma)))
      (1 / 4)) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L sigma, d = x + y := by
  have htau : 0 < 2 * bohrSumThreshold K L rho sigma :=
    mul_pos (by norm_num) (bohrSumThreshold_bounds K L hrho.le hsigma.le).1
  have htau1 : 2 * bohrSumThreshold K L rho sigma ≤ 1 := by
    have := bohrSumThreshold_le_quarter K L rho sigma
    linarith
  apply bohr_sum_of_common_spectrum_quarter K L hrho.le hsigma.le d
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  have hlarge := (Finset.mem_filter.mp hr).2
  have hK := large_bohr_fourier_mem_uniform_boundedSpan K (half_pos hrho)
    (by linarith : rho / 2 < 1 / 2) htau htau1 hlarge.1
  have hL := large_bohr_fourier_mem_uniform_boundedSpan L (half_pos hsigma)
    (by linarith : sigma / 2 < 1 / 2) htau htau1 hlarge.2
  exact (Finset.mem_filter.mp hd).2 r (Finset.mem_inter.mpr ⟨hK, hL⟩)


/-- A common cutoff for two Bohr sets whose ranks are at most r. -/
theorem bohr_sum_contains_rank_cap_span_quarter {N : Nat} [NeZero N] [Fact N.Prime]
    (K L : Finset (ZMod N)) (r M : Nat) [NeZero M]
    (hK : K.card ≤ r) (hL : L.card ≤ r) {rho : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hM : 2 ≤ rho * M) (d : ZMod N)
    (hd : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N))
        (polynomialSpectrumCutoff r (rho / 2) (2 * bohrSumRankThreshold r r M M)) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N))
        (polynomialSpectrumCutoff r (rho / 2) (2 * bohrSumRankThreshold r r M M)))
      (1 / 4)) :
    ∃ x ∈ bohr K rho, ∃ y ∈ bohr L rho, d = x + y := by
  have htpos : 0 < 2 * bohrSumRankThreshold r r M M :=
    mul_pos (by norm_num) (bohrSumRankThreshold_pos r r M M)
  have ht : 2 * bohrSumRankThreshold r r M M ≤ 2 * bohrSumThreshold K L rho rho := by
    have h := (bohrSumRankThreshold_antitone_ranks hK hL M).trans
      (bohrSumRankThreshold_le K L M M hM hM)
    linarith
  have hRK := (polynomialSpectrumCutoff_antitone K.card (half_pos hrho) htpos ht).trans
    (polynomialSpectrumCutoff_mono_rank hK (half_pos hrho) htpos)
  have hRL := (polynomialSpectrumCutoff_antitone L.card (half_pos hrho) htpos ht).trans
    (polynomialSpectrumCutoff_mono_rank hL (half_pos hrho) htpos)
  apply bohr_sum_contains_span_intersection_uniform_quarter K L hrho hrho1 hrho hrho1 d
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q hq => ?_⟩
  obtain ⟨hqK, hqL⟩ := Finset.mem_inter.mp hq
  exact (Finset.mem_filter.mp hd).2 q (Finset.mem_inter.mpr
    ⟨boundedFrequencySpan_mono _ hRK hqK, boundedFrequencySpan_mono _ hRL hqL⟩)


end LeanProofs.GowersSzemeredi
