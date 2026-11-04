import Trace74Width3GraphJoin
import Trace74NearDiagonalFixedClient

/-! Width-three conditional separation for the fixed-symbolic first port. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74Width3FixedClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74Width3GraphJoin Trace74NearDiagonalFixedClient
open CompactFixedBeta Trace74FixedQLarge Trace74FixedBeta31
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- Retain the linked fixed-symbolic witnesses and sharpen their separation
when the first index is at least twelve. -/
theorem fixed_exists_width3_indices (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n r : V, 7≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 ∧
      11≤r ∧ n+2<r ∧ r<2*n ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) ∧
      (12≤n → n+3<r) := by
  obtain ⟨n,r,hn,hny,hmod,hr11,hnr,hr2,hodd,hc⟩ := fixed_exists_separated_indices p v hp0 hv hz
  have hb31 : (31:V)≤(p 0:V) := by rw [hp0]; exact beta_ge_31
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : (1073741824:V)≤q p v := fixed_q_large p v hp0 (hv 0)
  refine ⟨n,r,hn,hny,hmod,hr11,hnr,hr2,hodd,hc,?_⟩
  intro hn12
  by_contra hsep
  exact graph_width3_large_q_impossible p v n r hb hv hz hn12 (le_of_not_gt hsep) hq hny hc

#print axioms Trace74Width3FixedClient.fixed_exists_width3_indices
end Trace74Width3FixedClient
