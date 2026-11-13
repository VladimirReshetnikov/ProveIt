import Trace74NearDiagonalGraphJoin
import Trace74FixedMainIndexEleven

/-! Linked-index and fixed-symbolic clients of the near-diagonal exclusion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74NearDiagonalFixedClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74NearDiagonalGraphJoin Trace74FixedMainIndexEleven
open CompactFixedBeta Trace74FixedQLarge Trace74FixedBeta31
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- A linked main index at least eleven is more than two above the first
index, independently of whether the first index equals seven. -/
theorem graph_main_separated (p : Fin 4 → ℕ) (v : Fin 10 → V) (n r : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hq : (1073741824:V)≤q p v) (hr11 : (11:V)≤r)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : c p v=ycoord r (A p v-1)) : n+2<r := by
  by_contra hsep
  have hr : r≤n+2 := le_of_not_gt hsep
  have hn8 : (8:V)≤n := by
    by_contra hn
    have hnlt : n<8 := lt_of_not_ge hn
    have hrlt : r<10 := calc
      r≤n+2 := hr
      _<8+2 := by simpa only [add_comm] using add_lt_add_right hnlt 2
      _=10 := by norm_num
    exact (not_lt_of_ge hr11) (lt_of_lt_of_le hrlt (by norm_num))
  exact graph_near_diagonal_large_q_impossible p v n r hb hv hz hn8 hr hq hny hc

/-- All indices are for one positive graph zero; only the first symbolic
port is fixed here, and the other three remain arbitrary. -/
theorem fixed_exists_separated_indices (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n r : V, 7≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 ∧
      11≤r ∧ n+2<r ∧ r<2*n ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) := by
  obtain ⟨n,r,hn,hny,hmod,hr11,hnr,hr2,hodd,hc⟩ := fixed_exists_indices p v hp0 hv hz
  have hb31 : (31:V)≤(p 0:V) := by rw [hp0]; exact beta_ge_31
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : (1073741824:V)≤q p v := fixed_q_large p v hp0 (hv 0)
  exact ⟨n,r,hn,hny,hmod,hr11,graph_main_separated p v n r hb hv hz hq hr11 hny hc,hr2,hodd,hc⟩

#print axioms Trace74NearDiagonalFixedClient.graph_main_separated
#print axioms Trace74NearDiagonalFixedClient.fixed_exists_separated_indices
end Trace74NearDiagonalFixedClient
