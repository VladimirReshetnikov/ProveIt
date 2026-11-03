import Trace75IntegralTransport

/-! Translate the actual signed transport into its positive natural mask equation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75NaturalTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75
open Trace75Factors Trace75Transport Trace75IntegralTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Cnat (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := q p v-v 1-v 2

theorem graph_natural_transport (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ t : V, 0<Cnat p v ∧ ((p 1:V)+v 5)*Cnat p v=v 1+b p v*t := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hbeta31
  have hmask := (graph_transport_and_mask p v hb hv hz).2
  have hFle : v 1≤q p v := le_trans (by simp) (le_of_lt hmask)
  have hsub : q p v-v 1+v 1=q p v := tsub_add_cancel_of_le hFle
  have halpha : v 2<q p v-v 1 := by
    apply (add_lt_add_iff_right (v 1)).mp
    rw [hsub,add_comm (v 2) (v 1)]
    exact hmask
  have hC : 0<Cnat p v := tsub_pos_iff_lt.mpr halpha
  have hcast1 : (ι (q p v-v 1):DiffRing V)=ι (q p v)-ι (v 1) := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,hsub]
  have hcast2 : (ι (Cnat p v):DiffRing V)=ι (q p v-v 1)-ι (v 2) := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add]
    change ι ((q p v-v 1-v 2)+v 2)=ι (q p v-v 1)
    rw [tsub_add_cancel_of_le (le_of_lt halpha)]
  obtain ⟨t,ht⟩ := graph_integral_transport p v hbeta31 hl hh hv hz
  have hqeval : (regs (ports p) (fun j => ι (v j))).q=ι (q p v) := by
    simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hBeval : (regs (ports p) (fun j => ι (v j))).B=
      ι ((p 1:V)+v 5)*ι (Cnat p v)-ι (v 1) := by
    simp only [B_def,C_def,ports,hqeval,map_add,map_natCast,hcast2,hcast1]
  have hcast : (ι (((p 1:V)+v 5)*Cnat p v):DiffRing V)=ι (v 1+b p v*t) := by
    rw [hBeval] at ht
    simp only [map_mul,map_add] at ht ⊢
    linear_combination ht
  exact ⟨t,hC,ι_injective hcast⟩

#print axioms Trace75NaturalTransport.graph_natural_transport
end Trace75NaturalTransport
