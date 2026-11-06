import DiophantineConsistency.Compact44.FixedGraphSafeSource
/-! Width-121 port of `Compact44/TemporalShiftSplit` by `research/mixed121-calibration/tools/width_port.py`: the accepted proof
body with the width literals 67/66/65 replaced by 121/120/119. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace W121.TemporalShiftSplit
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reduced (n E : V) (hn : 0<n) :
    let q := (E/121)%n
    let r := E%121
    E%(121*n)=121*q+r ∧ q<n ∧ r<121 := by
  dsimp only
  have h := mod_mul_split E (121:V) n (by norm_num) hn
  refine ⟨?_,mod_lt _ hn,mod_lt _ (by norm_num)⟩
  rw [h]
  ring
#print axioms W121.TemporalShiftSplit.reduced
end W121.TemporalShiftSplit
