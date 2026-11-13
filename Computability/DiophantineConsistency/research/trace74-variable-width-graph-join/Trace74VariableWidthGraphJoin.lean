import Trace74VariableWidthAmplification
import Trace74PellGapBinding
import Trace74UniformGraphHeight
import Trace74IndexOrder
import Trace74FixedQSymbolicBound
import Trace74FixedBeta31

/-! Same-zero variable-width obstruction with explicit threshold. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74VariableWidthGraphJoin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74PellGapBinding Trace74IndexOrder
open Trace74VariableWidthPellHeight Trace74VariableWidthSizeModel Trace74VariableWidthAmplification
open Trace74UniformGraphHeight Trace74FixedQSymbolicBound Trace74FixedBeta31 CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- A same-zero variable-width obstruction. The explicit model equation
`e+w=3(m+1)` and threshold are not derived from the graph. -/
theorem graph_variable_width_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (m w r B e : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hq : power 2 B≤q p v)
    (hr : r≤(m+3*w+1)+w)
    (he : e+w=3*(m+1))
    (hsize : 2*w*((m+3*w+1)+w)+5*w≤B*e)
    (hny : 2*ycoord (m+3*w+1) (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) : False := by
  let n : V := m+3*w+1
  let s : V := r-1
  have hn1 : (1:V)≤n := by dsimp [n]; simp
  have hnr : n<r := graph_first_lt_odd p v n r hb hv hny hc
  have hr2 : (2:V)≤r := by
    have hnlt : (1:V)<r := lt_of_le_of_lt hn1 hnr
    simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp hnlt
  have hr1 : (1:V)≤r := le_trans (by norm_num) hr2
  have hs : s+1=r := tsub_add_cancel_of_le hr1
  have hsle : s≤m+4*w := by
    apply (add_le_add_iff_right (1:V)).mp
    calc
      s+1=r := hs
      _≤(m+3*w+1)+w := hr
      _=(m+4*w)+1 := by ring
  have hqpos : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hypos : 0<Y p v := mul_pos (mul_pos (mul_pos hqpos hqpos) hqpos) (hv 6)
  have hY : 1≤Y p v := pos_iff_one_le.mp hypos
  have hq2 : (2:V)≤q p v := by
    unfold q b
    have hm : 1≤(p 0:V)*v 0 := one_le_mul (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
    calc
      (2:V)=1+1 := by norm_num
      _≤(p 0:V)*v 0+1 := by simpa only [add_comm] using add_le_add_right hm 1
  have hX : (2:V)≤X p v := calc
    (2:V)≤q p v := hq2
    _≤v 5*q p v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right (pos_iff_one_le.mp (hv 5)) (show (0:V)≤q p v by simp)
    _=X p v := rfl
  have hgap := tuple_pell_gap p v n r (hv 8) hny hc
  have hgap' : (2*Y p v)*ycoord ((m+3*w)+1) (2*(X p v*Y p v*Y p v-1)+1)<
      ycoord (s+1) (Y p v*(X p v+1)-1) := by
    simpa only [n,hs] using hgap
  have hsmall := pell_gap_height (X p v) (Y p v) m w s hX hY hsle hgap'
  have hy : q p v*q p v*q p v≤Y p v := by
    simpa only [Y,mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp (hv 6))
      (show (0:V)≤q p v*q p v*q p v by simp)
  have hh : b p v≤q p v := by change b p v≤b p v+1; simp
  have hlarge := lower_power_bound (q p v) (Y p v) (b p v) (Exp.exp r) B m w r e
    hq hy hh (power_two r).symm hr he hsize
  have hbig := amplified_height (X p v) (Y p v) (b p v) (Exp.exp r) m w hsmall hlarge
  have hbig' : 8*(b p v)*(Exp.exp r)^2*(Y p v)^2<X p v := by
    simpa only [pow_two,mul_assoc] using hbig
  exact graph_height_impossible p v r hb hv hz hr2 hc hbig'

/-- The full symbolic beta supplies the `q≥2^B` premise with fixed
`B=67*8807`; all threshold and ordinate premises remain explicit. -/
theorem fixed_graph_variable_width_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (m w r e : V) (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hr : r≤(m+3*w+1)+w) (he : e+w=3*(m+1))
    (hsize : 2*w*((m+3*w+1)+w)+5*w≤((67:V)*8807)*e)
    (hny : 2*ycoord (m+3*w+1) (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) : False := by
  have hb : 0<(p 0:V) := by
    rw [hp0]
    exact lt_of_lt_of_le (by norm_num : (0:V)<31) beta_ge_31
  have hq : power (2:V) ((67:V)*8807)≤q p v := by
    rw [power_two]
    exact fixed_q_symbolic_lower p v hp0 (hv 0)
  exact graph_variable_width_impossible p v m w r ((67:V)*8807) e hb hv hz hq hr he hsize hny hc

#print axioms Trace74VariableWidthGraphJoin.graph_variable_width_impossible
#print axioms Trace74VariableWidthGraphJoin.fixed_graph_variable_width_impossible
end Trace74VariableWidthGraphJoin
