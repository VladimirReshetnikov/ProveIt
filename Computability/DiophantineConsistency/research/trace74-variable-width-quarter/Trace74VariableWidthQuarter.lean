import Trace74VariableWidthIndexClient

/-! An index-dependent quarter-width specialization of the general threshold. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74VariableWidthQuarter
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74VariableWidthIndexClient CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- Sufficient arithmetic hypotheses for the general variable-width
threshold. `w` may be any positive internal index at most `n/4`. -/
theorem quarter_threshold (n w B : V) (hw : 1≤w) (h4 : 4*w≤n) (h8 : 8*n≤B) :
    3*w+1≤n ∧ 10*w≤3*n ∧ 2*w*(n+w)+5*w≤B*(3*n-10*w) := by
  let N : DiffRing V := ι n
  let W : DiffRing V := ι w
  let T : DiffRing V := ι B
  have hN : 0≤N := by
    dsimp [N]
    simpa only [map_zero] using ι_le_ι.mpr (show (0:V)≤n by simp)
  have hW : (1:DiffRing V)≤W := by dsimp [W]; simpa only [map_one] using ι_le_ι.mpr hw
  have h4R : 4*W≤N := by dsimp [W,N]; simpa only [map_mul,map_ofNat] using ι_le_ι.mpr h4
  have h8R : 8*N≤T := by dsimp [N,T]; simpa only [map_mul,map_ofNat] using ι_le_ι.mpr h8
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
  have hT : 0≤T := by
    dsimp [T]
    simpa only [map_zero] using ι_le_ι.mpr (show (0:V)≤B by simp)
  have hm1 := mul_nonneg (show (0:DiffRing V)≤N-4*W by linarith)
    (show (0:DiffRing V)≤N+W by linarith)
  have hm2 := mul_nonneg (show (0:DiffRing V)≤T-8*N by linarith) hN
  have hm3 := mul_nonneg (show (0:DiffRing V)≤N-W by linarith) hN
  have hm4 := mul_nonneg (show (0:DiffRing V)≤N-1 by linarith) hN
  have hL : 2*(2*W*(N+W)+5*W)≤T*N := by nlinarith
  have hTmul := mul_le_mul_of_nonneg_left hDlow hT
  have htarget : 2*W*(N+W)+5*W≤T*D := by nlinarith
  refine ⟨hn,he,?_⟩
  apply ι_le_ι.mp
  dsimp [N,W,T,D] at htarget
  simpa only [map_add,map_mul,map_ofNat] using htarget

/-- Same-zero fixed-symbolic quarter-width exclusion for any positive `w`
with `4w≤n` and `8n≤67*8807`. -/
theorem fixed_graph_quarter_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (n r w : V) (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hw : 1≤w) (h4 : 4*w≤n) (h8 : 8*n≤((67:V)*8807))
    (hr : r≤n+w)
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) : False := by
  obtain ⟨hn,he,hsize⟩ := quarter_threshold n w ((67:V)*8807) hw h4 h8
  exact fixed_graph_index_impossible p v n r w hp0 hv hz hn he hr hsize hny hc

#print axioms Trace74VariableWidthQuarter.quarter_threshold
#print axioms Trace74VariableWidthQuarter.fixed_graph_quarter_impossible
end Trace74VariableWidthQuarter
