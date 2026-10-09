import GowersSzemeredi.Proofs16BohrSpanExtension
import GowersSzemeredi.Proofs16BoundedSpanPhase

/-! Failure of Bohr-sum containment gives a frequency in the common
bounded span which escapes the prescribed bounded span of the selected frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Retain a witnessing point as well as the escaping frequency. -/
theorem bohr_sum_bounded_frequency_escape {N d : Nat} [NeZero N] [Fact N.Prime]
    (T U D : Finset (ZMod N)) (L : Nat) {r sigma : Real}
    (hr : 0 < r) (hr4 : r < 4) (hT : T.card ≤ d) (hU : U.card ≤ d)
    (hs : (D.card : Real)*L*sigma ≤ 1/(4*Real.pi))
    (hfail : ¬ bohr D sigma ⊆ bohrQuarterSum T U r) :
    ∃ y ∈ bohr D sigma, ∃ q ∈ bohrExtensionSpectrum T U d r,
      1/(4*Real.pi)*(N : Real) < centeredAbs (q*y) ∧
      q ∉ boundedFrequencySpan (fun a : D => (a : ZMod N)) L := by
  obtain ⟨y,hy,hyn⟩ : ∃ y ∈ bohr D sigma, y ∉ bohrQuarterSum T U r := by
    simpa only [Finset.subset_iff,not_forall,exists_prop] using hfail
  have hyK : y ∉ bohr (bohrExtensionSpectrum T U d r) (1/(4*Real.pi)) :=
    fun h => hyn (bohrExtensionSpectrum_subset_sum T U hr hr4 hT hU h)
  have hex : ∃ q ∈ bohrExtensionSpectrum T U d r,
      1/(4*Real.pi)*(N : Real) < centeredAbs (q*y) := by
    simpa only [bohr,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_le,exists_prop] using hyK
  obtain ⟨q,hq,hlarge⟩ := hex
  refine ⟨y,hy,q,hq,hlarge,?_⟩
  intro hqD
  have hphase := boundedFrequencySpan_phase_bound (fun a : D => (a : ZMod N)) L y
    (fun a => (Finset.mem_filter.mp hy).2 a a.property) hqD
  simp only [Fintype.card_coe] at hphase
  have hbound := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg N : (0 : Real) ≤ N)
  linarith

end LeanProofs.GowersSzemeredi
