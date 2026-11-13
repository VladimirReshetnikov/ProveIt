import Trace75ThreeTwo
import Trace75ThreeGap

/-! Exclude trace75 main index three when the radix is at least three. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75ThreeExcluded
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace75Pell Trace75ThreeTwo
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_three_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V) (n : V)
    (hb2 : 2≤(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0)
    (hfirst : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hmain : c p v=ycoord 3 (A p v-1)) : False := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by simp : (0:V)<2) hb2
  obtain ⟨_,hk,_,heq⟩ := graph_three_two_algebra p v n hb hv hz hfirst hmain
  have hJ1 : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hbge : 2≤b p v := le_trans hb2 (by
    change (p 0:V)≤(p 0:V)*v 0
    exact le_mul_of_one_le_right (by simp) hJ1)
  have hq3 : 3≤q p v := by
    simpa only [q,show (3:V)=2+1 by ring,add_comm] using _root_.add_le_add_right hbge (1:V)
  have hq2 : 2≤q p v := le_trans (by
    simpa only [show (3:V)=2+1 by ring] using (show (2:V)≤2+1 by simp)) hq3
  have hw1 : 1≤v 5 := pos_iff_one_le.mp (hv 5)
  have hs1 : 1≤v 6 := pos_iff_one_le.mp (hv 6)
  have hX2 : 2≤X p v := le_trans hq2 (by
    change q p v≤v 5*q p v
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (show (0:V)≤q p v by simp))
  have hq4 : 4≤q p v*q p v := by
    calc
      4=(2:V)*2 := by ring
      _≤q p v*q p v := mul_le_mul hq2 hq2 (by simp) (by simp)
  have hq8 : 8≤q p v*q p v*q p v := by
    calc
      8=(4:V)*2 := by ring
      _≤(q p v*q p v)*q p v := mul_le_mul hq4 hq2 (by simp) (by simp)
  have hY8 : 8≤Y p v := le_trans hq8 (by
    change q p v*q p v*q p v≤(q p v*q p v*q p v)*v 6
    exact le_mul_of_one_le_right (by simp) hs1)
  have hetaK : v 8<k v := by
    change v 8<v 8+v 9
    exact lt_add_of_pos_right _ (hv 9)
  have hX2r : (2:DiffRing V)≤ι (X p v) := by
    simpa only [map_ofNat] using (ι_le_ι.mpr hX2)
  have hY8r : (8:DiffRing V)≤ι (Y p v) := by
    simpa only [map_ofNat] using (ι_le_ι.mpr hY8)
  have hetapos : (0:DiffRing V)<ι (v 8) := by
    simpa only [map_zero] using (ι_lt_ι.mpr (hv 8))
  have hetaupper : (ι (v 8):DiffRing V)<8*ι (X p v)*(ι (Y p v))^2+4 := by
    have h := ι_lt_ι.mpr hetaK
    rw [hk] at h
    simpa only [map_add,map_mul,map_ofNat,pow_two,mul_assoc] using h
  obtain ⟨hsmall,hclose⟩ := Trace75ThreeGap.gap_bounds
    (ι (X p v):DiffRing V) (ι (Y p v)) (ι (v 8)) hX2r hY8r hetapos hetaupper heq
  have hsmallV : X p v<2*Y p v := ι_lt_ι.mp (by
    simpa only [map_mul,map_ofNat] using hsmall)
  have hcloseV : 2*Y p v<X p v+3 := ι_lt_ι.mp (by
    simpa only [map_mul,map_add,map_ofNat] using hclose)
  let t : V := q p v*q p v*v 6
  have hX : X p v=q p v*v 5 := by dsimp [X]; ring
  have hY : Y p v=q p v*t := by dsimp [Y,t]; ring
  have hwlt : v 5<2*t := by
    have hlt : q p v*v 5<q p v*(2*t) := calc
      q p v*v 5=X p v := hX.symm
      _<2*Y p v := hsmallV
      _=q p v*(2*t) := by rw [hY]; ring
    by_contra hn
    have hle : 2*t≤v 5 := le_of_not_gt hn
    have hm := mul_le_mul_of_nonneg_left hle (show (0:V)≤q p v by simp)
    exact (not_le_of_gt hlt) hm
  have hwle : v 5+1≤2*t := lt_iff_succ_le.mp hwlt
  have hmult : q p v*(v 5+1)≤q p v*(2*t) := mul_le_mul_of_nonneg_left hwle (by simp)
  have hbig : X p v+q p v≤2*Y p v := by
    rw [hX,hY]
    calc
      q p v*v 5+q p v=q p v*(v 5+1) := by ring
      _≤q p v*(2*t) := hmult
      _=2*(q p v*t) := by ring
  have hge : X p v+3≤2*Y p v := le_trans
    (by simpa only [add_comm] using _root_.add_le_add_right hq3 (X p v)) hbig
  exact (not_le_of_gt hcloseV) hge

#print axioms Trace75ThreeExcluded.main_three_impossible
end Trace75ThreeExcluded
