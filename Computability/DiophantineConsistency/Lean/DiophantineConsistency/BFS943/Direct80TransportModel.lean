import DiophantineConsistency.BFS943.Direct80GraphCarrierBound
import DiophantineConsistency.BFS943.Direct80OffsetBound
import DiophantineConsistency.BFS943.Direct80TransportConditional
import DiophantineConsistency.BFS943.Direct80TransportMask

/-! Actual positive 80-graph zeros have nonnegative transport and positive mask. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80TransportModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80CarrierIdentity
open Direct80GraphCarrierBound TenPositive80OffsetBound TenPositive80TransportConditional TenPositive80TransportMask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_transport_and_mask (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    0≤(BExpr (integerPorts p)).evalRing (fun j => ι (v j)) ∧
      v 1+v 2<q p v := by
  obtain ⟨tau,f,V0,Z0,y,_ht,_hf,_hV,_hy,hVsq,hZsq,hZeq,hbound⟩ := graph_carrier_bound p v hb hv hz
  let Z : DiffRing V := (graph (integerPorts p)).z.evalRing (fun j => ι (v j))
  let mz : DiffRing V := ι (M p v)*ι (tau*f*y)
  have hsq : Z*Z=mz*mz := by
    calc
      Z*Z=ι (Z0*Z0) := hZsq
      _=mz*mz := by rw [hZeq]; dsimp [mz]; simp only [map_mul]; ring
  have hfactor : (Z-mz)*(Z+mz)=0 := by rw [show (Z-mz)*(Z+mz)=Z*Z-mz*mz by ring,hsq]; ring
  have hcarrier : ∃ z : DiffRing V, Z=ι (M p v)*z ∧ z≤ι (tau*f*y) := by
    rcases mul_eq_zero.mp hfactor with h|h
    · exact ⟨ι (tau*f*y),sub_eq_zero.mp h,le_rfl⟩
    · refine ⟨-ι (tau*f*y),?_,neg_le_self (ι_nonneg _)⟩
      have heq : Z= -mz := eq_neg_of_add_eq_zero_left h
      dsimp [mz] at heq
      simpa only [mul_neg] using heq
  obtain ⟨z,hZ,hzle⟩ := hcarrier
  have hboundR : (2:DiffRing V)*ι (tau*f*y)<ι (V0*V0) := by
    have h := ι_lt_ι.mpr hbound
    simpa only [map_mul,map_ofNat] using h
  have hzbound : 2*z < (graph (integerPorts p)).v.evalRing (fun j => ι (v j))*
      (graph (integerPorts p)).v.evalRing (fun j => ι (v j)) := by
    calc
      2*z≤2*ι (tau*f*y) := mul_le_mul_of_nonneg_left hzle (by norm_num)
      _<ι (V0*V0) := hboundR
      _=(graph (integerPorts p)).v.evalRing (fun j => ι (v j))*
        (graph (integerPorts p)).v.evalRing (fun j => ι (v j)) := hVsq.symm
  have hZ' : (graph (integerPorts p)).z.evalRing (fun j => ι (v j)) =
      (graph (integerPorts p)).m.evalRing (fun j => ι (v j))*z := by
    rw [M_eval p v hb hv]
    exact hZ
  have hB := graph_transport_nonnegative_of_bounds p v hb hv hz z hZ' hzbound (graph_offset_bound p v hb hv)
  exact ⟨hB,positive_mask_of_nonnegative_transport p v (hv 1) (hv 5) hB⟩

#print axioms TenPositive80TransportModel.graph_transport_and_mask
end TenPositive80TransportModel
