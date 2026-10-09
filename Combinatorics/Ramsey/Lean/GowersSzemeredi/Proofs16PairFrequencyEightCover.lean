import GowersSzemeredi.Proofs16ProgressionFreimanCells

/-! A selected frequency map has a finite, modulus-independent cover
of its actual domain by sets on which it is Freiman of order eight. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def PairFrequencyMap.eightCover {N : Nat} (g : PairFrequencyMap N) : Finset (Finset (ZMod N)) :=
  Finset.univ.image (translatedProgressionCell g.progression g.shift)

theorem PairFrequencyMap.eightCover_nonempty {N : Nat} (g : PairFrequencyMap N) :
    g.eightCover.Nonempty := Finset.univ_nonempty.image _

theorem PairFrequencyMap.eightCover_card_le {N : Nat} (g : PairFrequencyMap N) :
    g.eightCover.card ≤ 16^g.progression.rank := by
  exact Finset.card_image_le.trans_eq (by simp)

theorem PairFrequencyMap.eightCover_union {N : Nat} (g : PairFrequencyMap N) :
    g.eightCover.biUnion id = g.domain := by
  have he : g.eightCover.biUnion id = Finset.univ.biUnion
      (translatedProgressionCell g.progression g.shift) := by
    ext x
    simp [eightCover]
  exact he.trans (translatedProgressionCells_cover g.progression g.shift)

theorem PairFrequencyMap.eightCover_freiman {N : Nat} [NeZero N] (g : PairFrequencyMap N)
    (hP : g.progression.Proper) (hf : FreimanHom 2 g.domain g.toFun) :
    ∀ C ∈ g.eightCover, C ⊆ g.domain ∧ FreimanHom 8 C g.toFun := by
  intro C hC
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hC
  exact ⟨translatedProgressionCell_subset g.progression g.shift c,
    translatedProgressionCell_freiman_eight g.progression hP g.shift g.toFun hf c⟩

theorem PairFrequencyMap.joint_eightCover {N d : Nat} [NeZero N] (g : PairFrequencyMap N)
    {delta r : Real} (hg : g.JointControlled delta d r) :
    g.eightCover.Nonempty ∧ g.eightCover.card ≤ 16^(jointMapRank delta d r) ∧
      g.eightCover.biUnion id = g.domain ∧
      ∀ C ∈ g.eightCover, C ⊆ g.domain ∧ FreimanHom 8 C g.toFun := by
  obtain ⟨hrank,hP,hmass,hf⟩ := PairFrequencyMap.JointControlled.uniform_bounds g hg
  exact ⟨g.eightCover_nonempty,g.eightCover_card_le.trans (Nat.pow_le_pow_right (by omega) hrank),
    g.eightCover_union,g.eightCover_freiman hP hf⟩

end LeanProofs.GowersSzemeredi
