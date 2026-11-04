import Trace74AtLeastEightR11GraphExclusion
import Trace74NearDiagonalFixedClient

/-! Fixed-symbolic main-index improvement conditional on first index ≥8. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74FixedMainIndexThirteen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell CompactFixedBeta Trace74FixedBeta31 Trace74FixedQLarge
open Trace74FixedMainIndexEleven Trace74NearDiagonalFixedClient Trace74AtLeastEightR11GraphExclusion
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- Retain the same supplied first index; when it is at least eight,
the linked odd main index is at least thirteen. -/
theorem fixed_main_index_ge_thirteen (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn8 : (8:V)≤n)
    (hcoord : 2*ycoord n (2*(firstParam p v-1)+1)=k v) :
    ∃ r : V, 13≤r ∧ n+2<r ∧ r<2*n ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) := by
  have hb31 : (31:V)≤(p 0:V) := by rw [hp0]; exact beta_ge_31
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : (1073741824:V)≤q p v := fixed_q_large p v hp0 (hv 0)
  obtain ⟨r,hr11,hnr,hr2,hodd,hc⟩ := fixed_main_index_ge_eleven p v n hp0 hv hz hcoord
  have hrne11 : r≠11 := by
    intro he
    have hm : c p v=ycoord 11 (A p v-1) := by simpa only [he] using hc
    exact graph_r11_impossible p v n hb hv hz hq hn8 hcoord hm
  have hr12 : (12:V)≤r := by
    have hh : (11:V)<r := lt_of_le_of_ne hr11 (Ne.symm hrne11)
    simpa only [show (11:V)+1=12 by ring] using lt_iff_succ_le.mp hh
  have hrne12 : r≠12 := by
    intro he
    rw [he,show (12:V)=2*6 by ring,mod_mul_self_right] at hodd
    exact zero_ne_one hodd
  have hr13 : (13:V)≤r := by
    have hh : (12:V)<r := lt_of_le_of_ne hr12 (Ne.symm hrne12)
    simpa only [show (12:V)+1=13 by ring] using lt_iff_succ_le.mp hh
  exact ⟨r,hr13,graph_main_separated p v n r hb hv hz hq hr11 hcoord hc,hr2,hodd,hc⟩

#print axioms Trace74FixedMainIndexThirteen.fixed_main_index_ge_thirteen
end Trace74FixedMainIndexThirteen
