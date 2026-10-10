import GowersSzemeredi.Proofs16DirectedExceptionCore

/-! A finite family of translated anchor points simultaneously enters a
near-full core. Each translation charges a missing vertex at most once. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_common_translation_into_core {G I : Type*}
    [AddCommGroup G] [DecidableEq G] [Fintype I]
    (B D S : Finset G) (shifts : I → G)
    (hD : ∀ u ∈ B, ∀ i, u+shifts i ∈ D)
    (hsmall : Fintype.card I*(D \ S).card < B.card) :
    ∃ u ∈ B, ∀ i, u+shifts i ∈ S := by
  let Bad := fun i : I => B.filter fun u => u+shifts i ∉ S
  have hbad : ∀ i, (Bad i).card ≤ (D \ S).card := by
    intro i
    apply Finset.card_le_card_of_injOn (fun u => u+shifts i)
    · intro u hu
      exact Finset.mem_sdiff.mpr ⟨hD u (Finset.mem_filter.mp hu).1 i, (Finset.mem_filter.mp hu).2⟩
    · intro u _ v _ he
      exact add_right_cancel he
  by_contra h
  have hsub : B ⊆ Finset.univ.biUnion Bad := by
    intro u hu
    have hn : ¬∀ i, u+shifts i ∈ S := by intro hp; exact h ⟨u,hu,hp⟩
    obtain ⟨i,hi⟩ := not_forall.mp hn
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hu,hi⟩⟩
  have hc : B.card ≤ Fintype.card I*(D \ S).card := by
    calc B.card ≤ (Finset.univ.biUnion Bad).card := Finset.card_le_card hsub
      _ ≤ ∑ i, (Bad i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : I, (D \ S).card := Finset.sum_le_sum fun i _ => hbad i
      _ = _ := by simp
  omega

end LeanProofs.GowersSzemeredi
