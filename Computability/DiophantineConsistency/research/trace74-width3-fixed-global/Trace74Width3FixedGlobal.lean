import Trace74Width3FixedClient
import Trace74AtLeastEightR11GraphExclusion
import Trace74N10R13GraphExclusion

/-! Same-zero width-three separation at the fixed symbolic first port. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74Width3FixedGlobal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74Width3FixedClient
open CompactFixedBeta Trace74FixedQLarge Trace74FixedBeta31
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- One fixed-symbolic positive zero supplies linked indices with gap at
least four; all inherited ordinate and residue facts refer to that pair. -/
theorem fixed_exists_width3_global (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n r : V, 7≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 ∧
      11≤r ∧ n+3<r ∧ r<2*n ∧ r%2=1 ∧ c p v=ycoord r (A p v-1) := by
  obtain ⟨n,r,hn,hny,hmod,hr11,hnr,hr2,hodd,hc,hwidth⟩ :=
    fixed_exists_width3_indices p v hp0 hv hz
  have hb31 : (31:V)≤(p 0:V) := by rw [hp0]; exact beta_ge_31
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hq : (1073741824:V)≤q p v := fixed_q_large p v hp0 (hv 0)
  have hseparate : n+3<r := by
    by_cases hn12 : 12≤n
    · exact hwidth hn12
    · have hnlt : n<12 := lt_of_not_ge hn12
      have hnle : n≤11 := by
        apply lt_succ_iff_le.mp
        simpa only [show (11:V)+1=12 by norm_num] using hnlt
      by_cases hn10 : 10≤n
      · by_cases hn11 : 11≤n
        · have heq : n=11 := le_antisymm hnle hn11
          have hr14 : (14:V)≤r := by
            have h := lt_iff_succ_le.mp hnr
            rw [heq] at h
            simpa only [show (11:V)+2+1=14 by norm_num] using h
          have hrne : r≠14 := by
            intro he
            rw [he,show (14:V)=2*7 by ring,mod_mul_self_right] at hodd
            norm_num at hodd
          have hrgt : (14:V)<r := lt_of_le_of_ne hr14 (Ne.symm hrne)
          simpa only [heq,show (11:V)+3=14 by norm_num] using hrgt
        · have hnlt11 : n<11 := lt_of_not_ge hn11
          have hnle10 : n≤10 := by
            apply lt_succ_iff_le.mp
            simpa only [show (10:V)+1=11 by norm_num] using hnlt11
          have heq : n=10 := le_antisymm hnle10 hn10
          have hr13 : (13:V)≤r := by
            have h := lt_iff_succ_le.mp hnr
            rw [heq] at h
            simpa only [show (10:V)+2+1=13 by norm_num] using h
          have hrne : r≠13 := by
            intro he
            have hfirst : 2*ycoord 10 (2*(firstParam p v-1)+1)=k v := by simpa only [heq] using hny
            have hmain : c p v=ycoord 13 (A p v-1) := by simpa only [he] using hc
            exact Trace74N10R13GraphExclusion.graph_impossible p v hb hv hz hq hfirst hmain
          have hrgt : (13:V)<r := lt_of_le_of_ne hr13 (Ne.symm hrne)
          simpa only [heq,show (10:V)+3=13 by norm_num] using hrgt
      · have hnlt10 : n<10 := lt_of_not_ge hn10
        by_cases hn8 : 8≤n
        · have hrne : r≠11 := by
            intro he
            have hmain : c p v=ycoord 11 (A p v-1) := by simpa only [he] using hc
            exact Trace74AtLeastEightR11GraphExclusion.graph_r11_impossible p v n hb hv hz hq hn8 hny hmain
          have hrgt : (11:V)<r := lt_of_le_of_ne hr11 (Ne.symm hrne)
          have hr12 : (12:V)≤r := by simpa only [show (11:V)+1=12 by norm_num] using lt_iff_succ_le.mp hrgt
          have hr13 : (13:V)≤r := by
            by_contra h
            have hlt : r<13 := lt_of_not_ge h
            have hle : r≤12 := by
              apply lt_succ_iff_le.mp
              simpa only [show (12:V)+1=13 by norm_num] using hlt
            have he : r=12 := le_antisymm hle hr12
            rw [he,show (12:V)=2*6 by ring,mod_mul_self_right] at hodd
            norm_num at hodd
          have hn3 : n+3<13 := by
            have h := add_lt_add_right hnlt10 3
            calc
              n+3=3+n := by ring
              _<3+10 := h
              _=13 := by norm_num
          exact lt_of_lt_of_le hn3 hr13
        · have hnlt8 : n<8 := lt_of_not_ge hn8
          have hn3 : n+3<11 := by
            have h := add_lt_add_right hnlt8 3
            calc
              n+3=3+n := by ring
              _<3+8 := h
              _=11 := by norm_num
          exact lt_of_lt_of_le hn3 hr11
  exact ⟨n,r,hn,hny,hmod,hr11,hseparate,hr2,hodd,hc⟩

#print axioms Trace74Width3FixedGlobal.fixed_exists_width3_global
end Trace74Width3FixedGlobal
