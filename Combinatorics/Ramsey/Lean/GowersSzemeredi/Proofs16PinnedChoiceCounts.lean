import GowersSzemeredi.Definitions

/-! Exact coordinate-fibre counts for independent representation choices.
Only the queried coordinates appear in the denominator; choices at all
other progression points cancel rather than contributing a density loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def pinnedChoiceSets {I V : Type*} [DecidableEq I]
    (F : I → Finset V) (S : Finset I) (a : I → V) : I → Finset V :=
  fun i => if i ∈ S then {a i} else F i

theorem pinned_choice_box_eq_filter {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (S : Finset I) (a : I → V) (ha : ∀ i ∈ S, a i ∈ F i) :
    Fintype.piFinset (pinnedChoiceSets F S a) =
      (Fintype.piFinset F).filter fun f => ∀ i ∈ S, f i = a i := by
  ext f
  simp only [Fintype.mem_piFinset, Finset.mem_filter]
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro i
      by_cases hi : i ∈ S
      · have he : f i = a i := by simpa [pinnedChoiceSets, hi] using hf i
        exact he.symm ▸ ha i hi
      · simpa [pinnedChoiceSets, hi] using hf i
    · intro i hi
      simpa [pinnedChoiceSets, hi] using hf i
  · rintro ⟨hf, hp⟩ i
    by_cases hi : i ∈ S
    · simp [pinnedChoiceSets, hi, hp i hi]
    · simpa [pinnedChoiceSets, hi] using hf i

/-- The queried coordinate product exactly recovers the full choice count. -/
theorem pinned_choice_count_product {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (S : Finset I) (a : I → V) :
    (∏ i ∈ S, (F i).card)*(Fintype.piFinset (pinnedChoiceSets F S a)).card =
      (Fintype.piFinset F).card := by
  rw [Fintype.card_piFinset, Fintype.card_piFinset]
  have hp : (∏ i : I, (pinnedChoiceSets F S a i).card) =
      ∏ i ∈ Finset.univ \ S, (F i).card := by
    calc
      _ = ∏ i ∈ Finset.univ \ S, (pinnedChoiceSets F S a i).card := by
        apply (Finset.prod_subset Finset.sdiff_subset ?_).symm
        intro i hi hnot
        have hiS : i ∈ S := by simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hnot
        simp [pinnedChoiceSets, hiS]
      _ = _ := Finset.prod_congr rfl fun i hi => by
        simp [pinnedChoiceSets, (Finset.mem_sdiff.mp hi).2]
  rw [hp]
  simpa only [Finset.compl_eq_univ_sdiff] using Finset.prod_mul_prod_compl S (fun i => (F i).card)

/-- Four distinct queried indices have the exact product law. -/
theorem four_choice_fibre_count_product {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (q : Fin 4 → I) (hq : Function.Injective q) (b : Fin 4 → V)
    (hb : ∀ j, b j ∈ F (q j)) :
    (∏ j : Fin 4, (F (q j)).card)*
      ((Fintype.piFinset F).filter fun f => ∀ j, f (q j) = b j).card = (Fintype.piFinset F).card := by
  let S := Finset.univ.image q
  let a : I → V := fun i => b (Function.invFun q i)
  have haq : ∀ j, a (q j) = b j := by
    intro j
    dsimp only [a]
    rw [Function.leftInverse_invFun hq j]
  have ha : ∀ i ∈ S, a i ∈ F i := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    rw [haq]
    exact hb j
  have hfilter : ((Fintype.piFinset F).filter fun f => ∀ j, f (q j) = b j) =
      Fintype.piFinset (pinnedChoiceSets F S a) := by
    rw [pinned_choice_box_eq_filter F S a ha]
    apply Finset.filter_congr
    intro f hf
    constructor
    · intro h i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      rw [haq]
      exact h j
    · intro h j
      exact (h (q j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)).trans (haq j)
  have hprod : (∏ i ∈ S, (F i).card) = ∏ j : Fin 4, (F (q j)).card := by
    exact Finset.prod_image (fun i hi j hj he => hq he)
  rw [hfilter, ←hprod]
  exact pinned_choice_count_product F S a

end LeanProofs.GowersSzemeredi
