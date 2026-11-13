import DiophantineConsistency.FixedGraphSafeSource
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TemporalShiftSplit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reduced (n E : V) (hn : 0<n) :
    let q := (E/67)%n
    let r := E%67
    E%(67*n)=67*q+r ∧ q<n ∧ r<67 := by
  dsimp only
  have h := mod_mul_split E (67:V) n (by norm_num) hn
  refine ⟨?_,mod_lt _ hn,mod_lt _ (by norm_num)⟩
  rw [h]
  ring
#print axioms TemporalShiftSplit.reduced
end TemporalShiftSplit
