import Trace74GraphRoots
import Trace75Residue

/-! UNCHECKED DRAFT. The synthetic old coordinate may be negative; these five
registers ignore that coordinate and retain their natural representatives. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74Representatives
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def masked (p : Fin 4 → ℕ) (v : Fin 10 → V) : Fin 10 → DiffRing V :=
  Trace74Mask.oldVal (ports p) (fun j => ι (v j))

theorem zero (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    value75 (ports p) (masked p v)=0 := by
  change value75 (ports p) (Trace74Mask.oldVal (ports p) (fun j => ι (v j)))=0
  rw [←Trace74Mask.coordinate_identity]
  exact hz

theorem delta_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    (regs (ports p) (masked p v)).Delta=ι (delta p v) := by
  change (regs (ports p) (fun j => ι (v j))).Delta=ι (delta p v)
  exact Trace75Factors.delta_eval p v

theorem U_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    (regs (ports p) (masked p v)).U=ι (U p v) := by
  change (regs (ports p) (fun j => ι (v j))).U=ι (U p v)
  exact Trace75Factors.U_eval p v

theorem E_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    (regs (ports p) (masked p v)).E=ι (E p v) := by
  change (regs (ports p) (fun j => ι (v j))).E=ι (E p v)
  exact Trace75Factors.E_eval p v

theorem M_eval (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    (regs (ports p) (masked p v)).M=ι (M p v) := by
  change (regs (ports p) (fun j => ι (v j))).M=ι (M p v)
  exact Trace75Factors.M_eval p v hb hv

theorem c_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    (regs (ports p) (masked p v)).c=ι (c p v) := by
  change (regs (ports p) (fun j => ι (v j))).c=ι (c p v)
  exact Trace75Residue.c_eval p v

#print axioms Trace74Representatives.zero
#print axioms Trace74Representatives.delta_eval
#print axioms Trace74Representatives.U_eval
#print axioms Trace74Representatives.E_eval
#print axioms Trace74Representatives.M_eval
#print axioms Trace74Representatives.c_eval
end Trace74Representatives
