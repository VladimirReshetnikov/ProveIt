import DiophantineConsistency.Compact44.TemporalCarryReset
import DiophantineConsistency.Compact44.CompactConcreteIndexedMass
import DiophantineConsistency.Compact44.CompactModelStencilSlack
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ConcreteCarryRoom
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open CompactGenericAlignedMass CompactConcreteIndexedMass
attribute [local irreducible] Compact943Data.rows selectors copies
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sum_generic {ι : Type*} (s : Finset ι) (f : ι→ℕ) :
    ((∑ j ∈ s,f j:ℕ):V)=∑ j ∈ s,(f j:V) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha,Nat.cast_add,ih]

theorem aligned_room :
    (∑ j : Aligned (Fin 943) (Fin 41), (alignedCoeff selectors copies j:V)*3)+1 < Exp.exp 66 := by
  have hm := congrArg (fun z : ℕ => (z:V)) concrete_mass
  simp only [Nat.cast_add,Nat.cast_one,cast_sum_generic] at hm
  have hs : (∑ j : Aligned (Fin 943) (Fin 41), (alignedCoeff selectors copies j:V)) ≤
      (CompactCoefficientMass.stencilMass:V) := by
    rw [←hm]
    exact le_add_of_nonneg_right (by simp)
  have h3 : (∑ j : Aligned (Fin 943) (Fin 41), (alignedCoeff selectors copies j:V)*3) ≤
      3*(CompactCoefficientMass.stencilMass:V) := by
    rw [←Finset.sum_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hs (by simp : (0:V)≤3)
  exact lt_of_le_of_lt (add_le_add h3 (le_refl _)) CompactModelStencilSlack.stencil_below_half
#print axioms ConcreteCarryRoom.aligned_room
end ConcreteCarryRoom
