import Trace75OldTraceOutput
import Trace74BoundaryParentWitness

/-! UNCHECKED DRAFT: candidate zero from same-witness parent Pell parts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74BoundaryPartsWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75OldTraceMap Trace75OldTraceOutput Trace74BoundaryParentWitness Trace74Mask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_74_of_parts (p : Fin 4 → DiffRing V) (v : Fin 10 → V)
    (c f d r mask tau f0 y u I : V) (hc : 0<c) (hf : 0<f) (hu : 0<u)
    (hmask : 0<mask) (hv : ∀ j,j ≠ 2 → 0<v j)
    (hmask' : (ι mask:DiffRing V)=(p 0*ι (v 0)+1)-ι (v 1)-ι (v 2))
    (hc' : (ι c:DiffRing V)=(regs p (fun j => ι (v j))).c)
    (hf' : (ι f:DiffRing V)=(regs p (fun j => ι (v j))).f)
    (hr' : (ι r:DiffRing V)=(regs p (fun j => ι (v j))).rank)
    (hd' : (ι d:DiffRing V)=2*(regs p (fun j => ι (v j))).Delta*(ι (v 3))^2*
      (regs p (fun j => ι (v j))).c^3*(regs p (fun j => ι (v j))).E)
    (hE : (regs p (fun j => ι (v j))).E=ι tau*ι tau)
    (hf0 : (regs p (fun j => ι (v j))).F0=ι f0*ι f0)
    (hQ : (regs p (fun j => ι (v j))).Q=ι I*ι I)
    (hV : oldV p (fun j => ι (v j))=ι u)
    (hZ : oldZ p (fun j => ι (v j))=(regs p (fun j => ι (v j))).M*(ι tau*ι f0*ι y))
    (haux : (ι I:DiffRing V)*ι I*ι u*ι u+ι y*ι y=1+ι I*ι I*ι y*ι y) :
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ w 0=v 0 ∧ w 1=v 1 ∧ w 2=mask ∧
      value74 p (fun j => ι (w j))=0 := by
  have hVpos : 0<oldV p (fun j => ι (v j)) := by
    rw [hV]
    simpa only [map_zero] using (ι_lt_ι.mpr hu)
  have hz := old_output_zero p (fun j => ι (v j)) (ι tau) (ι f0) (ι y) (ι u) (ι I)
    hE hf0 hQ hV hZ haux
  exact positive_74_of_parent p v c f d r mask hc hf hmask hv hmask' hc' hf' hr' hd' hVpos hz

#print axioms Trace74BoundaryPartsWitness.positive_74_of_parts
end Trace74BoundaryPartsWitness
