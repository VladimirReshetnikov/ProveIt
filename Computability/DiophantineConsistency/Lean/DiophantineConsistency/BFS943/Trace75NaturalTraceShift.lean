import DiophantineConsistency.BFS943.Trace75PositiveTraceShift
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ArithmeticPellRecurrence

/-! Positive natural witness for the squared-to-linear trace shift. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75NaturalTraceShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem natural_shift (c f d T r : V)
    (hc : 0<c) (hf : 0<f) (hshape : f=1+c*d)
    (hv : (0:DiffRing V)<ι f*ι f*(ι c*ι T-ι r)-ι c) :
    ∃ Tnew : V, 0<Tnew ∧
      (ι Tnew:DiffRing V)=ι f*ι T-ι d*ι r ∧
      ι f*(ι c*ι Tnew-ι r)-ι c=ι f*ι f*(ι c*ι T-ι r)-ι c := by
  have hc' : (0:DiffRing V)<ι c := by simpa only [map_zero] using (ι_lt_ι.mpr hc)
  have hf' : (0:DiffRing V)<ι f := by simpa only [map_zero] using (ι_lt_ι.mpr hf)
  have hshape' : (ι f:DiffRing V)=1+ι c*ι d := by rw [hshape]; simp only [map_add,map_one,map_mul]
  obtain ⟨hpos,heq⟩ := Trace75PositiveTraceShift.positive_shift (ι c) (ι f) (ι d) (ι T) (ι r)
    hc' hf' (ι_nonneg r) hshape' hv
  have hlt' : (ι (d*r):DiffRing V)<ι (f*T) := by simp only [map_mul]; linarith
  have hlt : d*r<f*T := ι_lt_ι.mp hlt'
  let Tnew := f*T-d*r
  have hTnew : 0<Tnew := tsub_pos_iff_lt.mpr hlt
  have hadd : Tnew+d*r=f*T := tsub_add_cancel_of_le (le_of_lt hlt)
  have hcast : (ι Tnew:DiffRing V)=ι f*ι T-ι d*ι r := by
    have h := congrArg (ι : V →+* DiffRing V) hadd
    simp only [map_add,map_mul] at h
    linarith
  exact ⟨Tnew,hTnew,hcast,by rw [hcast]; exact heq⟩

#print axioms Trace75NaturalTraceShift.natural_shift
end Trace75NaturalTraceShift
