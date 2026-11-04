import DiophantineConsistency.Compact44.CompactHighOriginTransfer
import DiophantineConsistency.Compact44.CompactHighResidue
import DiophantineConsistency.Compact44.CompactSymbolicPorts

/-! High-origin transfer from model remainders and its symbolic-mask instance. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactHighOriginResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticBinaryCarry ArithmeticWindowDigits
open CompactHighOriginTransfer CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem transfer_residue (x m : V) (hx : x % 4 = 0) (hm : m % 8 = 4)
    (h : NoCarry x m) : NoCarry x (m-1) := by
  have hxrep : 4*(x/4) = x := by simpa [hx] using div_add_mod x 4
  have hmrep : 8*(m/8)+4 = m := by simpa [hm] using div_add_mod m 8
  have hmminus : m-1 = 8*(m/8)+3 := by
    calc
      m-1 = (8*(m/8)+4)-1 := congrArg (fun z : V => z-1) hmrep.symm
      _ = 8*(m/8)+3 := by
        have h4 : (4:V) = 3+1 := by norm_num
        rw [h4, ← add_assoc, add_tsub_cancel_right]
  have hbase : NoCarry (4*(x/4)) (8*(m/8)+4) := by simpa only [hxrep, hmrep] using h
  have hc := transfer_parts (x/4) (m/8) hbase
  simpa only [hxrep, ← hmminus] using hc

theorem symbolic_high_origin (x : V) (hx : x % 4 = 0)
    (h : NoCarry x (highNat : V)) : NoCarry x ((highNat : V)-1) := by
  apply transfer_residue x (highNat : V) hx
  · exact CompactHighResidue.model_mod_eight
  · exact h

#print axioms CompactHighOriginResidue.transfer_residue
#print axioms CompactHighOriginResidue.symbolic_high_origin
end CompactHighOriginResidue
