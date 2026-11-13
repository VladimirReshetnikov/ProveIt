import DiophantineConsistency.ModelDifferenceRing
import Model69GraphCut

/-! Experimental exact subtraction mapping for a natural-like arithmetic model.
This file does not yet connect a carrier zero to the graph cut. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69ViewMap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing
open Model69GraphCutDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem map_sub_of_le (a b : V) (h : b≤a) :
    (ι (a-b) : DiffRing V) = ι a - ι b := by
  apply eq_sub_iff_add_eq.mpr
  have hh := congrArg (ι : V → DiffRing V) (tsub_add_cancel_of_le h)
  simpa only [map_add] using hh

end Model69ViewMap
#print axioms Model69ViewMap.map_sub_of_le
