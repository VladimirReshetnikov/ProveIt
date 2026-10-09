import GowersSzemeredi.Proofs16BohrSumExtension
import GowersSzemeredi.Proofs16BohrSumRankCap

/-! Local map extension on the intersection of bounded frequency spans,
with a coefficient cutoff and rank cap independent of the modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def bohrExtensionCutoff (d : Nat) (r : Real) : Nat :=
  polynomialSpectrumCutoff d (r/8) (bohrSumRankThreshold d d ⌈8/r⌉₊ ⌈8/r⌉₊)

def bohrExtensionSpectrum {N : Nat} [NeZero N] (T U : Finset (ZMod N)) (d : Nat) (r : Real) :
    Finset (ZMod N) :=
  boundedFrequencySpan (fun t : T => (t : ZMod N)) (bohrExtensionCutoff d r) ∩
    boundedFrequencySpan (fun u : U => (u : ZMod N)) (bohrExtensionCutoff d r)

theorem bohrExtensionSpectrum_card_le {N d : Nat} [NeZero N]
    (T U : Finset (ZMod N)) (r : Real) (hT : T.card ≤ d) :
    (bohrExtensionSpectrum T U d r).card ≤ (2*bohrExtensionCutoff d r+1)^d := by
  calc _ ≤ (boundedFrequencySpan (fun t : T => (t : ZMod N)) (bohrExtensionCutoff d r)).card :=
      Finset.card_le_card Finset.inter_subset_left
    _ ≤ (2*bohrExtensionCutoff d r+1)^T.card := by
      simpa only [Fintype.card_coe] using boundedFrequencySpan_card_le
        (fun t : T => (t : ZMod N)) (bohrExtensionCutoff d r)
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hT

/-- The explicit intersection-spectrum Bohr set lies in the quarter sum. -/
theorem bohrExtensionSpectrum_subset_sum {N d : Nat} [NeZero N] [Fact N.Prime]
    (T U : Finset (ZMod N)) {r : Real} (hr : 0 < r) (hr4 : r < 4)
    (hT : T.card ≤ d) (hU : U.card ≤ d) :
    bohr (bohrExtensionSpectrum T U d r) (1/(4*Real.pi)) ⊆ bohrQuarterSum T U r := by
  have hM : 0 < ⌈8/r⌉₊ := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero ⌈8/r⌉₊ := ⟨hM.ne'⟩
  have hcells : 2 ≤ (r/4)*⌈8/r⌉₊ := by
    have h := (div_le_iff₀ hr).mp (Nat.le_ceil (8/r))
    nlinarith only [h]
  intro z hz
  have hz' : z ∈ bohr
      (boundedFrequencySpan (fun t : T => (t : ZMod N))
        (polynomialSpectrumCutoff d ((r/4)/2) (bohrSumRankThreshold d d ⌈8/r⌉₊ ⌈8/r⌉₊)) ∩
       boundedFrequencySpan (fun u : U => (u : ZMod N))
        (polynomialSpectrumCutoff d ((r/4)/2) (bohrSumRankThreshold d d ⌈8/r⌉₊ ⌈8/r⌉₊)))
      (1/(4*Real.pi)) := by
    simpa only [bohrExtensionSpectrum,bohrExtensionCutoff,div_div,show (4 : Real)*2 = 8 by norm_num] using hz
  obtain ⟨a,ha,b,hb,he⟩ := bohr_sum_contains_rank_cap_span T U d ⌈8/r⌉₊ hT hU
    (by positivity : 0 < r/4) (by linarith : r/4 < 1) hcells z hz'
  exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,he.symm⟩

/-- The chosen sum extension is Freiman-linear on the explicit Bohr set. -/
theorem bohrSumExtension_freiman_span {N d : Nat} [NeZero N] [Fact N.Prime]
    (T U : Finset (ZMod N)) (f g : ZMod N → ZMod N) {r : Real}
    (hr : 0 < r) (hr4 : r < 4) (hT : T.card ≤ d) (hU : U.card ≤ d)
    (hf : IsFreimanLinearOn (bohr T r) f) (hg : IsFreimanLinearOn (bohr U r) g)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hfg : ∀ z ∈ bohr T r, z ∈ bohr U r → f z = g z) :
    IsFreimanLinearOn (bohr (bohrExtensionSpectrum T U d r) (1/(4*Real.pi)))
      (bohrSumExtension T U f g r) :=
  (bohrSumExtension_freiman T U f g hr.le hf hg hf0 hg0 hfg).mono
    (bohrExtensionSpectrum_subset_sum T U hr hr4 hT hU)

end LeanProofs.GowersSzemeredi
