import DiophantineConsistency.Sign33StrongF
import Sign33OrderedRing

/-! Transport strong-norm and half-window consequences to the difference ring. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33InnerVRing
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem inner_v_of_window_and_strong (a c T r f i : V)
    (hc : 0<c) (hT : 0<T) (hf : 0<f) (hi : 0<i)
    (hhalf : 2*r<c)
    (hstrict : f*f=1+delta a*(i*c*c)*(i*c*c)) :
    0 ≤ ι c*ι T-ι r ∧ 0 ≤ ι f*ι f*(ι c*ι T-ι r)-ι c := by
  have hf2 : (2:V) ≤ f := Sign33StrongF.strong_norm_f_ge_two a c f i hc hf hi hstrict
  have hTR : (1 : DiffRing V) ≤ ι T := by
    simpa only [map_one] using (ι_le_ι.mpr (pos_iff_one_le.mp hT))
  have hfR : (2 : DiffRing V) ≤ ι f := by
    simpa only [map_ofNat] using (ι_le_ι.mpr hf2)
  have hcR : (0 : DiffRing V) < ι c := by
    simpa only [map_zero] using (ι_lt_ι.mpr hc)
  have hhR : (2 : DiffRing V)*ι r < ι c := by
    simpa only [map_mul, map_ofNat] using (ι_lt_ι.mpr hhalf)
  exact Sign33OrderedRing.inner_V_signs (ι c) (ι T) (ι r) (ι f) hcR hTR hhR hfR
end DiophantineConsistency.Sign33InnerVRing
#print axioms DiophantineConsistency.Sign33InnerVRing.inner_v_of_window_and_strong
