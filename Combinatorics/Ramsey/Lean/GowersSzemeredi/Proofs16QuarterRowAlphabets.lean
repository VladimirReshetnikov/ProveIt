import GowersSzemeredi.Proofs16UniformQuarterBohrSum
import GowersSzemeredi.Proofs16DenseRowAlphabets

/-! Quarter-radius directional containment, with the smaller coefficient
cutoff supplied by the doubled Fourier threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def directionalQuarterSpanCutoff (r M : Nat) (rho : Real) : Nat :=
  polynomialSpectrumCutoff (2 * r) (rho / 2) (2 * bohrSumRankThreshold (2 * r) (2 * r) M M)

/-- The improved threshold never enlarges the row alphabet cutoff. -/
theorem directionalQuarterSpanCutoff_le (r M : Nat) [NeZero M]
    {rho : Real} (hrho : 0 < rho) :
    directionalQuarterSpanCutoff r M rho ≤ directionalSpanCutoff r M rho := by
  have ht := bohrSumRankThreshold_pos (2 * r) (2 * r) M M
  exact polynomialSpectrumCutoff_antitone _ (half_pos hrho) ht (by linarith)

/-- The next horizontal difference contains the Bohr set of the common
row-difference frequencies, with one cutoff for all four rows. -/
theorem directional_bohr_span_quarter {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    (Gamma : ZMod N → Finset (ZMod N)) (r M : Nat) [NeZero M]
    (hGamma : ∀ t, (Gamma t).card ≤ r) {rho : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hM : 2 ≤ rho * M)
    (hrows : ∀ t ∈ Y, ∀ x ∈ bohr (Gamma t) rho, (x, t) ∈ A)
    (y z w d : ZMod N) (hyz : y + z ∈ Y) (hz : z ∈ Y) (hyw : y + w ∈ Y) (hw : w ∈ Y)
    (hd : d ∈ bohr
      (frequencyDifference (rowSpanAlphabet Gamma (directionalQuarterSpanCutoff r M rho) (y + z))
          (rowSpanAlphabet Gamma (directionalQuarterSpanCutoff r M rho) z) ∩
       frequencyDifference (rowSpanAlphabet Gamma (directionalQuarterSpanCutoff r M rho) (y + w))
          (rowSpanAlphabet Gamma (directionalQuarterSpanCutoff r M rho) w)) (1 / 4)) :
    (d, y) ∈ horDiff (verDiff A) := by
  let K := Gamma (y + z) ∪ Gamma z
  let L := Gamma (y + w) ∪ Gamma w
  have hK : K.card ≤ 2 * r := (Finset.card_union_le _ _).trans (by have := hGamma (y + z); have := hGamma z; omega)
  have hL : L.card ≤ 2 * r := (Finset.card_union_le _ _).trans (by have := hGamma (y + w); have := hGamma w; omega)
  have hcommon : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N)) (directionalQuarterSpanCutoff r M rho) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N)) (directionalQuarterSpanCutoff r M rho))
      (1 / 4) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q hq => ?_⟩
    obtain ⟨hqK, hqL⟩ := Finset.mem_inter.mp hq
    exact (Finset.mem_filter.mp hd).2 q (Finset.mem_inter.mpr
      ⟨boundedFrequencySpan_union_subset_difference _ _ _ hqK,
       boundedFrequencySpan_union_subset_difference _ _ _ hqL⟩)
  obtain ⟨u, hu, v, hv, hd'⟩ := bohr_sum_contains_rank_cap_span_quarter K L (2 * r) M hK hL hrho hrho1 hM d hcommon
  have hrowpair (t : ZMod N) (hyt : y + t ∈ Y) (ht : t ∈ Y) (x : ZMod N)
      (hx : x ∈ bohr (Gamma (y + t) ∪ Gamma t) rho) : (x, y) ∈ verDiff A := by
    have hx1 : x ∈ bohr (Gamma (y + t)) rho := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun q hq => (Finset.mem_filter.mp hx).2 q (Finset.mem_union_left _ hq)⟩
    have hx2 : x ∈ bohr (Gamma t) rho := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun q hq => (Finset.mem_filter.mp hx).2 q (Finset.mem_union_right _ hq)⟩
    simpa using mem_verDiff (hrows (y + t) hyt x hx1) (hrows t ht x hx2)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, -v,
    hrowpair z hyz hz u hu, hrowpair w hyw hw (-v) (neg_mem_bohr hv), by simpa using hd'⟩


/-- Dense rows produce finite alphabets containing zero and controlling the
four-direction difference set, uniformly in the prime modulus. -/
theorem dense_row_directional_alphabets_quarter {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    {delta : Real} (hdelta : 0 < delta)
    (hdense : ∀ y ∈ Y, delta ≤ (rowOf A y).card / (N : Real))
    (M : Nat) [NeZero M] (hM : 2 ≤ (1 / (8 * Real.pi)) * M) :
    ∃ U : ZMod N → Finset (ZMod N),
      (∀ y, (0 : ZMod N) ∈ U y ∧
        (U y).card ≤ (2 * directionalQuarterSpanCutoff ⌈16 * delta ^ (-(2 : Real))⌉₊ M
          (1 / (8 * Real.pi)) + 1) ^ ⌈16 * delta ^ (-(2 : Real))⌉₊) ∧
      ∀ y z w d : ZMod N, y + z ∈ Y → z ∈ Y → y + w ∈ Y → w ∈ Y →
        d ∈ bohr (frequencyDifference (U (y + z)) (U z) ∩
          frequencyDifference (U (y + w)) (U w)) (1 / 4) →
        (d, y) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  obtain ⟨Gamma, hGamma, hrows⟩ := dense_row_spectra A Y hdelta hdense
  let r := ⌈16 * delta ^ (-(2 : Real))⌉₊
  refine ⟨rowSpanAlphabet Gamma (directionalQuarterSpanCutoff r M (1 / (8 * Real.pi))),
    rowSpanAlphabet_bounds Gamma r _ hGamma, ?_⟩
  intro y z w d hyz hz hyw hw hd
  exact directional_bohr_span_quarter (horDiff (horDiff A)) Y Gamma r M hGamma
    (by positivity) (by have := Real.pi_gt_three; rw [div_lt_one (by positivity)]; linarith)
    hM hrows y z w d hyz hz hyw hw hd


end LeanProofs.GowersSzemeredi
