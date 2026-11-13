import Trace75OldTraceOutput
import Trace75OldTracePositiveMap

/-! Positive trace75 zero from matching squared-parent Pell/carrier parts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75OldTracePartsJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75OldTraceMap Trace75OldTraceOutput Trace75OldTracePositiveMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_of_parts (p : Fin 4 → DiffRing V) (v : Fin 10 → V)
    (c f d r tau f0 y u I : V) (hc : 0<c) (hf : 0<f) (hu : 0<u)
    (hv : ∀ j,0<v j)
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
    ∃ w : Fin 10 → V, (∀ j,0<w j) ∧ value75 p (fun j => ι (w j))=0 := by
  have hVpos : 0<oldV p (fun j => ι (v j)) := by
    rw [hV]
    simpa only [map_zero] using (ι_lt_ι.mpr hu)
  have hz := old_output_zero p (fun j => ι (v j)) (ι tau) (ι f0) (ι y) (ι u) (ι I)
    hE hf0 hQ hV hZ haux
  exact positive_parent_zero p v c f d r hc hf hv hc' hf' hr' hd' hVpos hz

#print axioms Trace75OldTracePartsJoin.positive_zero_of_parts
end Trace75OldTracePartsJoin
