import Trace74VariableWidthIndexClient
import Trace74Width3FixedGlobal

/-! A same-zero index gap with an internal minimum and no upper bound on n. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74VariableWidthMinimum
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74VariableWidthIndexClient Trace74Width3FixedGlobal CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- A uniform sufficient threshold for any positive model width at most
one quarter of the index and one eighth of the exponent bound. -/
theorem minimum_threshold (n w B : V) (hw : 1≤w) (h4 : 4*w≤n) (h8 : 8*w≤B) :
    3*w+1≤n ∧ 10*w≤3*n ∧ 2*w*(n+w)+5*w≤B*(3*n-10*w) := by
  let N : DiffRing V := ι n
  let W : DiffRing V := ι w
  let T : DiffRing V := ι B
  have hW : (1:DiffRing V)≤W := by dsimp [W]; simpa only [map_one] using ι_le_ι.mpr hw
  have h4R : 4*W≤N := by dsimp [W,N]; simpa only [map_mul,map_ofNat] using ι_le_ι.mpr h4
  have h8R : 8*W≤T := by dsimp [W,T]; simpa only [map_mul,map_ofNat] using ι_le_ι.mpr h8
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
  have hDlow : N≤2*D := by linarith
  have hDpos : 0≤D := by linarith
  have hWpos : 0≤W := by linarith
  have hp := mul_nonneg hWpos (show (0:DiffRing V)≤2*N-2*W-5 by linarith)
  have hL : 2*W*(N+W)+5*W≤4*W*N := by nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hDlow (show (0:DiffRing V)≤4*W by positivity)
  have hsecond := mul_le_mul_of_nonneg_right h8R hDpos
  have htarget : 2*W*(N+W)+5*W≤T*D := by nlinarith
  refine ⟨hn,he,?_⟩
  apply ι_le_ι.mp
  dsimp [N,W,T,D] at htarget
  simpa only [map_add,map_mul,map_ofNat] using htarget

/-- Fixed-symbolic same-zero exclusion with any positive width satisfying
the two size bounds; no upper bound on `n` is assumed. -/
theorem fixed_graph_width_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (n r w : V) (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hw : 1≤w) (h4 : 4*w≤n) (h8 : 8*w≤((67:V)*8807))
    (hr : r≤n+w)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) : False := by
  obtain ⟨hn,he,hsize⟩ := minimum_threshold n w ((67:V)*8807) hw h4 h8
  exact fixed_graph_index_impossible p v n r w hp0 hv hz hn he hr hsize hny hc

/-- `floor(n/4)` is positive whenever `n≥4`. -/
theorem quarter_positive (n : V) (hn : (4:V)≤n) : 1≤n/4 := by
  apply pos_iff_one_le.mp
  by_contra hnot
  have heq : n/4=0 := le_antisymm (le_of_not_gt hnot) (by simp)
  have hd := div_add_mod n (4:V)
  have hm : n%4<4 := mod_lt n (by norm_num)
  rw [heq,mul_zero,zero_add] at hd
  rw [hd] at hm
  exact (not_lt_of_ge hn) hm

/-- Same-zero lower separation for all internal first indices at least
four; the minimum saturates at the fixed symbolic exponent divided by 8. -/
theorem fixed_graph_minimum_separation (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (n r : V) (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn : (4:V)≤n)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) :
    n+min (n/4) 73758<r := by
  let w : V := min (n/4) 73758
  have hw : 1≤w := le_min (quarter_positive n hn) (by norm_num)
  have h4 : 4*w≤n := calc
    4*w≤4*(n/4) := mul_le_mul_of_nonneg_left (min_le_left _ _) (by simp)
    _≤n := mul_div_le n 4
  have h8 : 8*w≤((67:V)*8807) := calc
    8*w≤8*(73758:V) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by simp)
    _≤((67:V)*8807) := by norm_num
  by_contra hnot
  exact fixed_graph_width_impossible p v n r w hp0 hv hz hw h4 h8
    (le_of_not_gt hnot) hny hc

/-- One linked pair retains its original data and the new unbounded-index
minimum separation. -/
theorem fixed_exists_minimum_indices (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0) :
    ∃ n r : V, 7≤n ∧ 2*ycoord n (2*(firstParam p v-1)+1)=k v ∧
      k v%(q p v)^4=(2*n)%(q p v)^4 ∧
      11≤r ∧ n+3<r ∧ n+min (n/4) 73758<r ∧ r<2*n ∧ r%2=1 ∧
      Trace75Factors.c p v=ycoord r (A p v-1) := by
  obtain ⟨n,r,hn,hny,hmod,hr11,hnr,hr2,hodd,hc⟩ := fixed_exists_width3_global p v hp0 hv hz
  refine ⟨n,r,hn,hny,hmod,hr11,hnr,?_,hr2,hodd,hc⟩
  exact fixed_graph_minimum_separation p v n r hp0 hv hz (le_trans (by norm_num) hn) hny hc

#print axioms Trace74VariableWidthMinimum.minimum_threshold
#print axioms Trace74VariableWidthMinimum.fixed_graph_width_impossible
#print axioms Trace74VariableWidthMinimum.quarter_positive
#print axioms Trace74VariableWidthMinimum.fixed_graph_minimum_separation
#print axioms Trace74VariableWidthMinimum.fixed_exists_minimum_indices
end Trace74VariableWidthMinimum
