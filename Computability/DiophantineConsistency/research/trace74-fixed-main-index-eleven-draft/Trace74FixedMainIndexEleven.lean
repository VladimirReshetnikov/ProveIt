import Trace74MainIndexEleven
import Trace74FixedFirstIndexSeven
import Trace74FixedBeta31
import Trace74FixedQLarge
import Trace74Pell
import DiophantineConsistency.CompactFixedBeta

/-! Unchecked fixed-symbolic specialization; the same tuple and indices are retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74FixedMainIndexEleven
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open CompactFixedBeta Trace75Factors Trace74Pell Trace74FixedBeta31 Trace74FixedQLarge
open Trace74FixedFirstIndexSeven Trace74MainIndexEleven
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

theorem fixed_main_index_ge_eleven (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) :
    ∃ r : V, 11≤r ∧ n<r ∧ r<2*n ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) := by
  have hb31 : (31:V)≤(p 0:V) := by rw [hp0]; exact beta_ge_31
  have hb15 : (15:V)≤(p 0:V) := le_trans (by norm_num) hb31
  have hq64 : (64:V)≤q p v := le_trans (by norm_num) (fixed_q_large p v hp0 (hv 0))
  have hn7 : 7≤n := fixed_first_index_ge_seven p v n hp0 hv hz hcoord
  exact graph_main_index_ge_eleven p v n hb15 hv hz hq64 hn7 hcoord

theorem fixed_exists_indices (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n r : V, 7≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 ∧
      11≤r ∧ n<r ∧ r<2*n ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) := by
  obtain ⟨n,hn,hcoord,hmod⟩ := fixed_exists_first_index_ge_seven p v hp0 hv hz
  obtain ⟨r,hr,hnr,hr2,hodd,hc⟩ := fixed_main_index_ge_eleven p v n hp0 hv hz hcoord
  exact ⟨n,r,hn,hcoord,hmod,hr,hnr,hr2,hodd,hc⟩

#print axioms Trace74FixedMainIndexEleven.fixed_main_index_ge_eleven
#print axioms Trace74FixedMainIndexEleven.fixed_exists_indices
end Trace74FixedMainIndexEleven
