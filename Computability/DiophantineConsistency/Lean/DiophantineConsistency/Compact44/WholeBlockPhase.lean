import DiophantineConsistency.Compact44.FixedGraphCellShift
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace WholeBlockPhase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord
open CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem decoder_safe (p : V) (hp : p=4393 ∨ p=5495) : ¬Bad p := by
  rcases hp with rfl | rfl <;> norm_num [Bad]

theorem predecessor_safe (p : V) (hp : p=2195 ∨ p=3296 ∨ p=4393 ∨ p=5495) :
    ¬Bad (cyc 8807 p 1) := by
  have h1 : cyc (8807:V) 2195 1=2194 := by
    rw [cyc_of_le (by norm_num) (by norm_num) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (2194:V)+1=2195 by norm_num)).symm
  have h2 : cyc (8807:V) 3296 1=3295 := by
    rw [cyc_of_le (by norm_num) (by norm_num) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (3295:V)+1=3296 by norm_num)).symm
  have h3 : cyc (8807:V) 4393 1=4392 := by
    rw [cyc_of_le (by norm_num) (by norm_num) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (4392:V)+1=4393 by norm_num)).symm
  have h4 : cyc (8807:V) 5495 1=5494 := by
    rw [cyc_of_le (by norm_num) (by norm_num) (by norm_num)]
    exact (eq_tsub_of_add_eq (show (5494:V)+1=5495 by norm_num)).symm
  rcases hp with rfl | rfl | rfl | rfl <;> simp only [h1,h2,h3,h4] <;> norm_num [Bad]

theorem shift_phase (N k D : V) (hN : 0<N) (hD : D%8807=0) :
    (cyc (8807*N) k D)%8807=k%8807 := by
  rw [CyclicAnyPhase.cyc_period 8807 N k D (by norm_num) hN]
  unfold cyc
  rw [hD,tsub_zero,mod_add_remove_right (by norm_num : (0:V)<8807),
    mod_eq_self_of_lt (mod_lt k (by norm_num : (0:V)<8807))]
#print axioms WholeBlockPhase.decoder_safe
#print axioms WholeBlockPhase.predecessor_safe
#print axioms WholeBlockPhase.shift_phase
end WholeBlockPhase
