import Trace74Mask
import Trace75OldTraceMap
import Trace75NaturalTraceShift

/-! UNCHECKED DRAFT: positive 74 zero from a squared-parent zero while
    allowing the old third coordinate to be zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74BoundaryParentWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75OldTraceMap Trace74Mask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Draft: the new mask replaces the old third coordinate after the trace shift.
The old third coordinate need not be positive; all other source coordinates
are positive, and the new mask has an explicit positive representative. -/
theorem positive_74_of_parent (p : Fin 4 → DiffRing V) (v : Fin 10 → V)
    (c f d r mask : V) (hc : 0<c) (hf : 0<f) (hmask : 0<mask)
    (hv : ∀ j, j ≠ 2 → 0<v j)
    (hmask' : (ι mask:DiffRing V) = (p 0*ι (v 0)+1)-ι (v 1)-ι (v 2))
    (hc' : (ι c:DiffRing V)=(regs p (fun j => ι (v j))).c)
    (hf' : (ι f:DiffRing V)=(regs p (fun j => ι (v j))).f)
    (hr' : (ι r:DiffRing V)=(regs p (fun j => ι (v j))).rank)
    (hd' : (ι d:DiffRing V)=2*(regs p (fun j => ι (v j))).Delta*(ι (v 3))^2*
      (regs p (fun j => ι (v j))).c^3*(regs p (fun j => ι (v j))).E)
    (hV : 0<oldV p (fun j => ι (v j)))
    (hz : oldValue p (fun j => ι (v j))=0) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ w 0=v 0 ∧ w 1=v 1 ∧ w 2=mask ∧
      value74 p (fun j => ι (w j))=0 := by
  let z : Fin 10 → DiffRing V := fun j => ι (v j)
  have hshape : f=1+c*d := by
    apply ι_injective
    simp only [map_add,map_one,map_mul]
    rw [hf',hc',hd']
    exact f_one_mod_c p z
  have hV' : (0:DiffRing V)<ι f*ι f*(ι c*ι (v 4)-ι r)-ι c := by
    rw [hf',hc',hr']
    exact hV
  obtain ⟨T,hT,hTcast,_heq⟩ := Trace75NaturalTraceShift.natural_shift c f d (v 4) r hc hf hshape hV'
  let old : Fin 10 → V := Function.update v 4 T
  have hcast : (fun j => ι (old j))=shift p z := by
    funext j
    fin_cases j <;> simp [old,shift,z,hTcast,hf',hr',hd']
  have holdzero : value75 p (fun j => ι (old j))=0 := by
    rw [hcast,value_shift]
    exact hz
  let w : Fin 10 → V := Function.update old 2 mask
  have hw : ∀ j,0<w j := by
    intro j
    fin_cases j <;> simp [w,old,hmask,hT,hv]
  have hback : oldVal p (fun j => ι (w j)) = (fun j => ι (old j)) := by
    funext j
    fin_cases j <;> simp [oldVal,w,old,hmask']
  refine ⟨w,hw,?_,?_,?_,?_⟩
  · simp [w,old]
  · simp [w,old]
  · simp [w]
  · rw [coordinate_identity,hback]
    exact holdzero

#print axioms Trace74BoundaryParentWitness.positive_74_of_parent
end Trace74BoundaryParentWitness
