import GowersSzemeredi.Proofs16PairSelectionTermination

/-! Recover actual finite map indices for every selected frequency set,
without duplicates and with each required domain membership retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem PairSelectionState.pair_indices {N : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N)) {delta r : Real} {d : Nat}
    (hs : s.Valid T delta d r) (p : ZMod N × ZMod N) :
    ∃ I : Finset (Fin s.maps.length), I.card = (s.frequencies p).card ∧
      I.image (fun i => (s.maps.get i).toFun (p.1-p.2)) = s.frequencies p ∧
      ∀ i ∈ I, p.1-p.2 ∈ (s.maps.get i).domain := by
  have hex (v : s.frequencies p) : ∃ i : Fin s.maps.length,
      p.1-p.2 ∈ (s.maps.get i).domain ∧ (s.maps.get i).toFun (p.1-p.2) = (v : ZMod N) := by
    obtain ⟨g,hg,hdom,hval⟩ := hs.2.2.1 p v v.property
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hg
    exact ⟨i,by simpa only [hi] using hdom,by simpa only [hi] using hval⟩
  choose pick hdom hval using hex
  let I := Finset.univ.image pick
  have hinj : Function.Injective pick := by
    intro v w he
    apply Subtype.ext
    exact (hval v).symm.trans ((congrArg (fun i => (s.maps.get i).toFun (p.1-p.2)) he).trans (hval w))
  refine ⟨I,?_,?_,?_⟩
  · simp only [I,Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_coe]
  · ext v
    constructor
    · intro hv
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hi
      rw [hval w]
      exact w.property
    · intro hv
      exact Finset.mem_image.mpr ⟨pick ⟨v,hv⟩,
        Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩,hval ⟨v,hv⟩⟩
  · intro i hi
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hi
    exact hdom v

theorem PairSelectionState.index_family {N : Nat} [NeZero N]
    (s : PairSelectionState N) (T : ZMod N → Finset (ZMod N)) {delta r : Real} {d : Nat}
    (hs : s.Valid T delta d r) :
    ∃ I : (ZMod N × ZMod N) → Finset (Fin s.maps.length),
      ∀ p, (I p).card = (s.frequencies p).card ∧
        (I p).image (fun i => (s.maps.get i).toFun (p.1-p.2)) = s.frequencies p ∧
        ∀ i ∈ I p, p.1-p.2 ∈ (s.maps.get i).domain := by
  choose I hI using s.pair_indices T hs
  exact ⟨I,hI⟩

end LeanProofs.GowersSzemeredi
