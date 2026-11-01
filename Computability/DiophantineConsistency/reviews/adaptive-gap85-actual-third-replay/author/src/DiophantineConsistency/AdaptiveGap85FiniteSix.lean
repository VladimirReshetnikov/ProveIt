import DiophantineConsistency.AdaptiveGap85NegativeMultiplier
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FiniteSix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem one_to_six (n : V) (h1 : 1≤n) (hupper : n≤6) :
    n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 := by
  by_cases e1 : n=1
  · exact Or.inl e1
  have h2 : 2≤n := by
    simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp (lt_of_le_of_ne h1 (Ne.symm e1))
  by_cases e2 : n=2
  · exact Or.inr (Or.inl e2)
  have h3 : 3≤n := by
    simpa only [show (2:V)+1=3 by ring] using lt_iff_succ_le.mp (lt_of_le_of_ne h2 (Ne.symm e2))
  by_cases e3 : n=3
  · exact Or.inr (Or.inr (Or.inl e3))
  have h4 : 4≤n := by
    simpa only [show (3:V)+1=4 by ring] using lt_iff_succ_le.mp (lt_of_le_of_ne h3 (Ne.symm e3))
  by_cases e4 : n=4
  · exact Or.inr (Or.inr (Or.inr (Or.inl e4)))
  have h5 : 5≤n := by
    simpa only [show (4:V)+1=5 by ring] using lt_iff_succ_le.mp (lt_of_le_of_ne h4 (Ne.symm e4))
  by_cases e5 : n=5
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e5))))
  have h6 : 6≤n := by
    simpa only [show (5:V)+1=6 by ring] using lt_iff_succ_le.mp (lt_of_le_of_ne h5 (Ne.symm e5))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (le_antisymm hupper h6)))))
end DiophantineConsistency.AdaptiveGap85FiniteSix
