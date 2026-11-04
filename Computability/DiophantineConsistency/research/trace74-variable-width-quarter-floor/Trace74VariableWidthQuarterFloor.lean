import Trace74VariableWidthQuarter

/-! Same-zero fractional index separation with model division by four. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74VariableWidthQuarterFloor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace74Pell Trace74VariableWidthQuarter CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- For a positive fixed-symbolic graph zero with supplied same-tuple Pell
ordinates, first index at least four and at most one eighth of the fixed
beta exponent force the main index above `n+floor(n/4)`. -/
theorem fixed_graph_floor_separation (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (n r : V) (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn : (4:V)≤n) (h8 : 8*n≤((67:V)*8807))
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) : n+n/4<r := by
  have h4 : 4*(n/4)≤n := mul_div_le n 4
  have hdiv : 0<n/4 := by
    by_contra hnot
    have heq : n/4=0 := le_antisymm (le_of_not_gt hnot) (by simp)
    have hd := div_add_mod n (4:V)
    have hm : n%4<4 := mod_lt n (by norm_num)
    rw [heq,mul_zero,zero_add] at hd
    rw [hd] at hm
    exact (not_lt_of_ge hn) hm
  have hw : 1≤n/4 := pos_iff_one_le.mp hdiv
  by_contra hnot
  exact fixed_graph_quarter_impossible p v n r (n/4) hp0 hv hz hw h4 h8
    (le_of_not_gt hnot) hny hc

#print axioms Trace74VariableWidthQuarterFloor.fixed_graph_floor_separation
end Trace74VariableWidthQuarterFloor
