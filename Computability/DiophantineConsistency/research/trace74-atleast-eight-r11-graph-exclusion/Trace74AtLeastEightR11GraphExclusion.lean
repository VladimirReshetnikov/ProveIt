import Trace74N8R11GraphExclusion
import Trace74NearDiagonalGraphJoin

/-! General main-index eleven exclusion for first index at least eight. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74AtLeastEightR11GraphExclusion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74N8R11GraphExclusion Trace74NearDiagonalGraphJoin
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- No positive large-q trace74 zero has main index eleven and a supplied
first index at least eight on the same tuple. -/
theorem graph_r11_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hq : (1073741824:V)≤q p v) (hn : (8:V)≤n)
    (hfirst : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hmain : c p v=ycoord 11 (A p v-1)) : False := by
  rcases eq_or_lt_of_le hn with he | hlt
  · rw [←he] at hfirst
    exact graph_impossible p v hb hv hz hq hfirst hmain
  · have hsub : 0<n-8 := tsub_pos_of_lt hlt
    have h9 : (9:V)≤n := by
      have hp := add_le_add_right (pos_iff_one_le.mp hsub) (8:V)
      have he : (8:V)+(n-8)=n := by rw [add_comm,tsub_add_cancel_of_le hn]
      rw [he] at hp
      simpa only [show (8:V)+1=9 by norm_num] using hp
    have hr : (11:V)≤n+2 := by
      have hp := add_le_add_right h9 (2:V)
      calc
        (11:V)=2+9 := by norm_num
        _≤2+n := hp
        _=n+2 := by ring
    exact graph_near_diagonal_large_q_impossible p v n 11 hb hv hz hn hr hq hfirst hmain

#print axioms Trace74AtLeastEightR11GraphExclusion.graph_r11_impossible
end Trace74AtLeastEightR11GraphExclusion
