import Trace74VariableWidthMinimumSharp

/-! A complementary two-sevenths same-zero width, with no cap on n. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74VariableWidthTwoSevenths
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74VariableWidthIndexClient Trace74VariableWidthMinimumSharp CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- An affine threshold for positive widths at most two sevenths of the
first index. -/
theorem two_sevenths_threshold (n w B : V) (hw : 2≤w) (h7 : 7*w≤2*n)
    (hB : 18*w+10≤B) :
    3*w+1≤n ∧ 10*w≤3*n ∧ 2*w*(n+w)+5*w≤B*(3*n-10*w) := by
  let N : DiffRing V := ι n
  let W : DiffRing V := ι w
  let T : DiffRing V := ι B
  have hW : (2:DiffRing V)≤W := by dsimp [W]; simpa only [map_ofNat] using ι_le_ι.mpr hw
  have h7R : 7*W≤2*N := by dsimp [W,N]; simpa only [map_mul,map_ofNat] using ι_le_ι.mpr h7
  have hBR : 18*W+10≤T := by dsimp [W,T]; simpa only [map_add,map_mul,map_ofNat] using ι_le_ι.mpr hB
  have hR1 : 3*W+1≤N := by linarith
  have hR2 : 10*W≤3*N := by linarith
  have hn : 3*w+1≤n := by
    apply ι_le_ι.mp
    simpa only [map_add,map_mul,map_one,map_ofNat] using hR1
  have he : 10*w≤3*n := by
    apply ι_le_ι.mp
    simpa only [map_mul,map_ofNat] using hR2
  let D : DiffRing V := ι (3*n-10*w)
  have hD : D+10*W=3*N := by
    have hsub := tsub_add_cancel_of_le he
    have hi := congrArg (ι : V →+* DiffRing V) hsub
    dsimp [D,W,N]
    simpa only [map_add,map_mul,map_ofNat] using hi
  have hDpos : 0≤D := by linarith
  have hDeq : D=3*N-10*W := by linarith
  have hp := mul_nonneg (show (0:DiffRing V)≤2*N-7*W by linarith)
    (show (0:DiffRing V)≤52*W+30 by linarith)
  have hL : 2*(2*W*(N+W)+5*W)≤(36*W+20)*D := by
    rw [hDeq]
    nlinarith
  have hcoeff : 36*W+20≤2*T := by linarith
  have hsecond := mul_le_mul_of_nonneg_right hcoeff hDpos
  have htarget : 2*W*(N+W)+5*W≤T*D := by nlinarith
  refine ⟨hn,he,?_⟩
  apply ι_le_ι.mp
  dsimp [N,W,T,D] at htarget
  simpa only [map_add,map_mul,map_ofNat] using htarget

/-- The same-zero graph obstruction with an arbitrary width under the
two-sevenths threshold; no upper bound on n is assumed. -/
theorem fixed_graph_width_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (n r w : V) (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hw : 2≤w) (h7 : 7*w≤2*n) (hB : 18*w+10≤((67:V)*8807))
    (hr : r≤n+w)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) : False := by
  obtain ⟨hn,he,hsize⟩ := two_sevenths_threshold n w ((67:V)*8807) hw h7 hB
  exact fixed_graph_index_impossible p v n r w hp0 hv hz hn he hr hsize hny hc

/-- For `n≥7`, the model quotient `floor(2n/7)` is at least two. -/
theorem two_sevenths_at_least_two (n : V) (hn : (7:V)≤n) : 2≤(2*n)/7 := by
  by_contra hnot
  have hlt : (2*n)/7<2 := lt_of_not_ge hnot
  have hle : (2*n)/7≤1 := by
    apply lt_succ_iff_le.mp
    simpa only [show (1:V)+1=2 by norm_num] using hlt
  have hrem : (2*n)%7≤6 := by
    apply lt_succ_iff_le.mp
    simpa only [show (6:V)+1=7 by norm_num] using (mod_lt (2*n) (show (0:V)<7 by norm_num))
  have hd := div_add_mod (2*n) (7:V)
  have hupper : 2*n≤13 := calc
    2*n=7*((2*n)/7)+(2*n)%7 := hd.symm
    _≤7*1+6 := add_le_add (mul_le_mul_of_nonneg_left hle (by simp)) hrem
    _=13 := by norm_num
  have hlower : (14:V)≤2*n := by
    simpa only [show (2:V)*7=14 by norm_num] using mul_le_mul_of_nonneg_left hn (show (0:V)≤2 by simp)
  have : (14:V)≤13 := le_trans hlower hupper
  norm_num at this

/-- Same-zero separation for every internal first index at least seven. -/
theorem fixed_graph_two_sevenths_separation (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (n r : V) (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn : (7:V)≤n)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) :
    n+min ((2*n)/7) 32781<r := by
  let w : V := min ((2*n)/7) 32781
  have hw : 2≤w := le_min (two_sevenths_at_least_two n hn) (by norm_num)
  have h7 : 7*w≤2*n := calc
    7*w≤7*((2*n)/7) := mul_le_mul_of_nonneg_left (min_le_left _ _) (by simp)
    _≤2*n := mul_div_le (2*n) 7
  have hB : 18*w+10≤((67:V)*8807) := calc
    18*w+10≤18*(32781:V)+10 := by
      have hm : w≤(32781:V) := min_le_right _ _
      have hm18 : 18*w≤18*(32781:V) := mul_le_mul_of_nonneg_left hm (by simp)
      simpa only [add_comm] using add_le_add_right hm18 (10:V)
    _≤((67:V)*8807) := by norm_num
  by_contra hnot
  exact fixed_graph_width_impossible p v n r w hp0 hv hz hw h7 hB
    (le_of_not_gt hnot) hny hc

/-- One linked pair retains both complementary no-cap separations and
the inherited same-zero ordinate and residue facts. -/
theorem fixed_exists_both_indices (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n r : V, 7≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 ∧
      11≤r ∧ n+3<r ∧ n+min (n/4) 118013<r ∧
      n+min ((2*n)/7) 32781<r ∧ r<2*n ∧ r%2=1 ∧
      Trace75Factors.c p v=ycoord r (A p v-1) := by
  obtain ⟨n,r,hn,hny,hmod,hr11,hnr,hquarter,hr2,hodd,hc⟩ :=
    fixed_exists_minimum_indices p v hp0 hv hz
  exact ⟨n,r,hn,hny,hmod,hr11,hnr,hquarter,
    fixed_graph_two_sevenths_separation p v n r hp0 hv hz hn hny hc,hr2,hodd,hc⟩

#print axioms Trace74VariableWidthTwoSevenths.two_sevenths_threshold
#print axioms Trace74VariableWidthTwoSevenths.fixed_graph_width_impossible
#print axioms Trace74VariableWidthTwoSevenths.two_sevenths_at_least_two
#print axioms Trace74VariableWidthTwoSevenths.fixed_graph_two_sevenths_separation
#print axioms Trace74VariableWidthTwoSevenths.fixed_exists_both_indices
end Trace74VariableWidthTwoSevenths
