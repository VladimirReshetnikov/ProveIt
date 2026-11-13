import DiophantineConsistency.BFS943.DirectBFSModelMass

/-! Carry room of the direct-BFS aligned family: thrice its coefficient mass,
plus one, stays below `2^66` in every IΣ₁ model.

Reconstructed in the tree (the research source was never committed): a port of
`ConcreteCarryRoom.aligned_room` to `DirectBFSModelMass.selectors/copies`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSCarryRoom
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency CompactGenericAlignedMass
attribute [local irreducible] DirectBFSSymbolicKernel.rows DirectBFSModelMass.selectors DirectBFSModelMass.copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sum_generic {ι : Type*} (s : Finset ι) (f : ι→ℕ) :
    ((∑ j ∈ s,f j:ℕ):V)=∑ j ∈ s,(f j:V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha,Nat.cast_add,ih]

theorem aligned_room :
    (∑ j : Aligned (Fin 943) (Fin 41),
      (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V)*3)+1 < Exp.exp 66 := by
  have hm := congrArg (fun z : ℕ => (z:V)) DirectBFSModelMass.natural_mass
  simp only [Nat.cast_add,Nat.cast_one,cast_sum_generic] at hm
  have hs : (∑ j : Aligned (Fin 943) (Fin 41),
      (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V)) ≤
      (DirectBFSCoefficientMass.stencilMass:V) := by
    rw [←hm]
    exact le_add_of_nonneg_right (by simp)
  have h3 : (∑ j : Aligned (Fin 943) (Fin 41),
      (alignedCoeff DirectBFSModelMass.selectors DirectBFSModelMass.copies j:V)*3) ≤
      3*(DirectBFSCoefficientMass.stencilMass:V) := by
    rw [←Finset.sum_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hs (by simp : (0:V)≤3)
  exact lt_of_le_of_lt (add_le_add h3 (le_refl _)) DirectBFSModelMass.stencil_below_half
#print axioms DirectBFSCarryRoom.aligned_room
end DirectBFSCarryRoom
