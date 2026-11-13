import DiophantineConsistency.CompactConcreteMask
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
noncomputable section
namespace CompactSupportCard
open Finset CompactConcreteMask

theorem support_card : support.card=985 := by
  let A : Finset ℕ := range 943
  let B : Finset ℕ := Ico 983 993
  let C : Finset ℕ := Ico 1003 1012
  let D : Finset ℕ := Ico 1013 1032
  let E : Finset ℕ := {1063,1064,1095,2195,3296}
  let U : Finset ℕ := A∪B∪C∪D∪E
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [A,B,mem_range,mem_Ico] at hj hk
    omega
  have hABC : Disjoint (A∪B) C := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [A,B,C,mem_union,mem_range,mem_Ico] at hj hk
    omega
  have hABCD : Disjoint (A∪B∪C) D := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [A,B,C,D,mem_union,mem_range,mem_Ico] at hj hk
    omega
  have hABCDE : Disjoint (A∪B∪C∪D) E := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [A,B,C,D,E,mem_union,mem_range,mem_Ico,mem_insert,mem_singleton] at hj hk
    omega
  have hU : U.card=986 := by
    dsimp only [U]
    rw [card_union_of_disjoint hABCDE,card_union_of_disjoint hABCD,
      card_union_of_disjoint hABC,card_union_of_disjoint hAB]
    norm_num [A,B,C,D,E]
  have hone : 1∈U := by simp [U,A,B]
  have heq : support=U.erase 1 := by
    ext j
    simp [support,U,A,B,C,D,E, and_comm]
  rw [heq,card_erase_of_mem hone,hU]
end CompactSupportCard
#print axioms CompactSupportCard.support_card
