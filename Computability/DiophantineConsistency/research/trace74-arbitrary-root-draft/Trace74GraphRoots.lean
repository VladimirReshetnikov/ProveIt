import Trace74ArbitraryRootNonzero
import Trace75Factors
import Trace74Mask

/-! UNCHECKED DRAFT: the two root factors from a 74 zero with positive 74
witnesses, without assuming the reverse mask guard. The synthetic 75-coordinate
valuation lives in the difference ring and may have a negative coordinate 2. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74GraphRoots
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace74ArbitraryRootNonzero
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_roots (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j)) = 0) :
    ∃ tau f : V, 0<tau ∧ 0<f ∧ E p v=tau*tau ∧
      1+delta p v*U p v*U p v*E p v=f*f := by
  let w : Fin 10 → DiffRing V := Trace74Mask.oldVal (ports p) (fun j => ι (v j))
  have hz75 : value75 (ports p) w=0 := by
    rw [←Trace74Mask.coordinate_identity]
    exact hz
  obtain ⟨hdp,hup,hep,hmp⟩ := factors_positive p v hb hv
  have hd : (regs (ports p) w).Delta = ι (delta p v) := by
    have h := delta_eval p v
    simpa [w, Trace74Mask.oldVal, regs] using h
  have hu : (regs (ports p) w).U = ι (U p v) := by
    have h := U_eval p v
    simpa [w, Trace74Mask.oldVal, regs] using h
  have he : (regs (ports p) w).E = ι (E p v) := by
    have h := E_eval p v
    simpa [w, Trace74Mask.oldVal, regs] using h
  have hm : (regs (ports p) w).M = ι (M p v) := by
    have h := M_eval p v hb hv
    simpa [w, Trace74Mask.oldVal, regs] using h
  exact roots_of_positive_representatives (ports p) w (delta p v) (U p v) (E p v) (M p v)
    hdp hup hep hmp hd hu he hm hz75

#print axioms Trace74GraphRoots.graph_roots
end Trace74GraphRoots
