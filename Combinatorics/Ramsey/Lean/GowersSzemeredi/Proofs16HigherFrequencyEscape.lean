import GowersSzemeredi.Proofs16BohrBoundedFrequencyEscape
import GowersSzemeredi.Proofs16FourPairSpanDecomposition

/-! Failure of a higher Bohr containment supplies sixteen column values
whose four left differences equal their four right differences and escape
a prescribed coefficient span of the selected frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherLeftFrequencies {N : Nat} (T : ZMod N → Finset (ZMod N)) (p : Fin 16 → ZMod N) : Finset (ZMod N) :=
  eightFrequencyUnion (fun i => T (p (Fin.castAdd 8 i)))

def higherRightFrequencies {N : Nat} (T : ZMod N → Finset (ZMod N)) (p : Fin 16 → ZMod N) : Finset (ZMod N) :=
  eightFrequencyUnion (fun i => T (p (Fin.natAdd 8 i)))

def higherLeftFrequencyValue {N : Nat} (v : Fin 16 → ZMod N) : ZMod N :=
  fourPairDifferenceSum (fun i => v (Fin.castAdd 8 i))

def higherRightFrequencyValue {N : Nat} (v : Fin 16 → ZMod N) : ZMod N :=
  fourPairDifferenceSum (fun i => v (Fin.natAdd 8 i))

def HigherFrequencyEquation {N : Nat} (v : Fin 16 → ZMod N) : Prop :=
  higherLeftFrequencyValue v = higherRightFrequencyValue v

theorem higher_column_frequency_escape {N d : Nat} [NeZero N] [Fact N.Prime]
    (T : ZMod N → Finset (ZMod N)) (D : Finset (ZMod N))
    (p : Fin 16 → ZMod N) (L : Nat) {r sigma : Real}
    (hr : 0 < r) (hr4 : r < 4) (hT : ∀ i, (T (p i)).card ≤ d)
    (hs : (D.card : Real)*L*sigma ≤ 1/(4*Real.pi))
    (hfail : ¬ bohr D sigma ⊆ bohrQuarterSum (higherLeftFrequencies T p) (higherRightFrequencies T p) r) :
    ∃ v : Fin 16 → ZMod N,
      (∀ i, v i ∈ boundedFrequencySpan (fun a : T (p i) => (a : ZMod N)) (bohrExtensionCutoff (8*d) r)) ∧
      HigherFrequencyEquation v ∧
      higherLeftFrequencyValue v ∉ boundedFrequencySpan (fun a : D => (a : ZMod N)) L := by
  obtain ⟨y,hy,q,hq,_,hqD⟩ := bohr_sum_bounded_frequency_escape
    (higherLeftFrequencies T p) (higherRightFrequencies T p) D L hr hr4
    (eightFrequencyUnion_card_le _ (fun i => hT _))
    (eightFrequencyUnion_card_le _ (fun i => hT _)) hs hfail
  obtain ⟨v,hv,hvsum⟩ := boundedFrequencySpan_eight_union_differences
    (fun i => T (p (Fin.castAdd 8 i))) _ (Finset.mem_inter.mp hq).1
  obtain ⟨w,hw,hwsum⟩ := boundedFrequencySpan_eight_union_differences
    (fun i => T (p (Fin.natAdd 8 i))) _ (Finset.mem_inter.mp hq).2
  let u : Fin 16 → ZMod N := fun i => Fin.addCases v w i
  have hu : ∀ i, u i ∈ boundedFrequencySpan (fun a : T (p i) => (a : ZMod N))
      (bohrExtensionCutoff (8*d) r) := by
    intro i
    refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i
    · simpa only [u,Fin.addCases_left] using hv j
    · simpa only [u,Fin.addCases_right] using hw j
  have hleft : higherLeftFrequencyValue u = fourPairDifferenceSum v := by
    simp only [higherLeftFrequencyValue,u,Fin.addCases_left]
  have hright : higherRightFrequencyValue u = fourPairDifferenceSum w := by
    simp only [higherRightFrequencyValue,u,Fin.addCases_right]
  refine ⟨u,hu,?_,?_⟩
  · exact hleft.trans (hvsum.symm.trans (hwsum.trans hright.symm))
  · rw [hleft,← hvsum]
    exact hqD

end LeanProofs.GowersSzemeredi
