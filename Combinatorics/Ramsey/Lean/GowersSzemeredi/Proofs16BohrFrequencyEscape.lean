import GowersSzemeredi.Proofs16BohrSpanExtension
import GowersSzemeredi.Proofs16BoundedSpanPhase

/-! Failure of Bohr-sum containment gives a frequency in the common
bounded span which escapes the unit span of the selected frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Retain a witnessing point as well as the escaping frequency. -/
theorem bohr_sum_frequency_escape {N d : Nat} [NeZero N] [Fact N.Prime]
    (T U D : Finset (ZMod N)) {r sigma : Real}
    (hr : 0 < r) (hr4 : r < 4) (hT : T.card ≤ d) (hU : U.card ≤ d)
    (hs : (D.card : Real)*sigma ≤ 1/(4*Real.pi))
    (hfail : ¬ bohr D sigma ⊆ bohrQuarterSum T U r) :
    ∃ y ∈ bohr D sigma, ∃ q ∈ bohrExtensionSpectrum T U d r,
      1/(4*Real.pi)*(N : Real) < centeredAbs (q*y) ∧
      q ∉ boundedFrequencySpan (fun a : D => (a : ZMod N)) 1 := by
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
  have hphase := boundedFrequencySpan_phase_bound (fun a : D => (a : ZMod N)) 1 y
    (fun a => (Finset.mem_filter.mp hy).2 a a.property) hqD
  simp only [Fintype.card_coe,Nat.cast_one,mul_one] at hphase
  have hbound := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg N : (0 : Real) ≤ N)
  linarith

/-- Splitting the two union spans produces four admissible frequency
values with equal differences outside the selected unit span. -/
theorem column_pair_frequency_escape {N d : Nat} [NeZero N] [Fact N.Prime]
    (T : ZMod N → Finset (ZMod N)) (D : Finset (ZMod N))
    (p : Fin 4 → ZMod N) {r sigma : Real}
    (hr : 0 < r) (hr4 : r < 4) (hT : ∀ i, (T (p i)).card ≤ d)
    (hs : (D.card : Real)*sigma ≤ 1/(4*Real.pi))
    (hfail : ¬ bohr D sigma ⊆ bohrQuarterSum (T (p 0) ∪ T (p 1)) (T (p 2) ∪ T (p 3)) r) :
    ∃ v : Fin 4 → ZMod N,
      (∀ i, v i ∈ boundedFrequencySpan (fun a : T (p i) => (a : ZMod N)) (bohrExtensionCutoff (2*d) r)) ∧
      v 0-v 1 = v 2-v 3 ∧
      v 0-v 1 ∉ boundedFrequencySpan (fun a : D => (a : ZMod N)) 1 := by
  have hcap (i j : Fin 4) : (T (p i) ∪ T (p j)).card ≤ 2*d :=
    (Finset.card_union_le _ _).trans ((Nat.add_le_add (hT i) (hT j)).trans (by omega))
  obtain ⟨y,hy,q,hq,_,hqD⟩ := bohr_sum_frequency_escape
    (T (p 0) ∪ T (p 1)) (T (p 2) ∪ T (p 3)) D hr hr4 (hcap 0 1) (hcap 2 3) hs hfail
  obtain ⟨a,ha,b,hb,hab⟩ := boundedFrequencySpan_union_difference _ _ _ (Finset.mem_inter.mp hq).1
  obtain ⟨c,hc,e,he,hce⟩ := boundedFrequencySpan_union_difference _ _ _ (Finset.mem_inter.mp hq).2
  refine ⟨![a,b,c,e],?_,?_,?_⟩
  · intro i; fin_cases i <;> assumption
  · exact hab.symm.trans hce
  · exact hab ▸ hqD

end LeanProofs.GowersSzemeredi
