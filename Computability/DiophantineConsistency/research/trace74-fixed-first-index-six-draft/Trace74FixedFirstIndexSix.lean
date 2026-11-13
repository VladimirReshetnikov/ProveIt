import Trace74FixedBeta31
import Trace74FixedQLarge
import Trace74FirstIndexSix
import Trace74Pell
import DiophantineConsistency.CompactFixedBeta

/-! Unchecked fixed-beta specialization; same tuple and index retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74FixedFirstIndexSix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open CompactFixedBeta Trace75Factors Trace74Pell Trace74FixedBeta31 Trace74FixedQLarge Trace74FirstIndexSix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

theorem fixed_first_index_ge_six (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) : 6≤n := by
  have hb31 : (31:V)≤(p 0:V) := by rw [hp0]; exact beta_ge_31
  have hq := fixed_q_large p v hp0 (hv 0)
  exact graph_first_index_ge_six p v n hb31 hv hz hq hcoord

theorem fixed_exists_first_index_ge_six (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n : V, 6≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 := by
  have hb31 : (31:V)≤(p 0:V) := by rw [hp0]; exact beta_ge_31
  have hq := fixed_q_large p v hp0 (hv 0)
  exact graph_exists_first_index_ge_six p v hb31 hv hz hq

#print axioms Trace74FixedFirstIndexSix.fixed_first_index_ge_six
#print axioms Trace74FixedFirstIndexSix.fixed_exists_first_index_ge_six
end Trace74FixedFirstIndexSix
