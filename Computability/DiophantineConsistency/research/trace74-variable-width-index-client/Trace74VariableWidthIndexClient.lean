import Trace74VariableWidthGraphJoin

/-! Direct-index clients of the variable-width model obstruction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace74VariableWidthIndexClient
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence ArithmeticPow
open Trace75Factors Trace74Pell Trace74VariableWidthGraphJoin CompactFixedBeta
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] CompactFixedBeta.betaNat

/-- Direct-index version of the same-zero variable-width obstruction.
The two subtraction bounds and quantitative threshold are explicit. -/
theorem graph_index_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (n r B w : V) (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hq : power 2 B≤q p v) (hn : 3*w+1≤n) (he : 10*w≤3*n)
    (hr : r≤n+w) (hsize : 2*w*(n+w)+5*w≤B*(3*n-10*w))
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) : False := by
  let m : V := n-(3*w+1)
  let e : V := 3*n-10*w
  have hm : m+3*w+1=n := by
    have ht : m+(3*w+1)=n := tsub_add_cancel_of_le hn
    simpa only [add_assoc] using ht
  have het : e+10*w=3*n := tsub_add_cancel_of_le he
  have heq : e+w=3*(m+1) := by
    apply add_right_cancel (b := (9*w))
    calc
      e+w+9*w=e+10*w := by ring
      _=3*n := het
      _=3*(m+1)+9*w := by rw [←hm]; ring
  have hr' : r≤(m+3*w+1)+w := by rw [hm]; exact hr
  have hsize' : 2*w*((m+3*w+1)+w)+5*w≤B*e := by
    rw [hm]
    exact hsize
  have hny' : 2*ycoord (m+3*w+1) (2*(firstParam p v-1)+1)=k v := by
    rw [hm]
    exact hny
  exact graph_variable_width_impossible p v m w r B e hb hv hz hq hr' heq hsize' hny' hc

/-- Direct-index specialization using the full symbolic first-port lower
bound on `q`. The quantitative threshold remains explicit. -/
theorem fixed_graph_index_impossible (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (n r w : V) (hp0 : p 0=betaNat) (hv : ∀j,0<v j)
    (hz : Trace74Mask.value74 (ports p) (fun j => ι (v j))=0)
    (hn : 3*w+1≤n) (he : 10*w≤3*n) (hr : r≤n+w)
    (hsize : 2*w*(n+w)+5*w≤((67:V)*8807)*(3*n-10*w))
    (hny : 2*ycoord n (2*(firstParam p v-1)+1)=k v)
    (hc : Trace75Factors.c p v=ycoord r (A p v-1)) : False := by
  let m : V := n-(3*w+1)
  let e : V := 3*n-10*w
  have hm : m+3*w+1=n := by
    have ht : m+(3*w+1)=n := tsub_add_cancel_of_le hn
    simpa only [add_assoc] using ht
  have het : e+10*w=3*n := tsub_add_cancel_of_le he
  have heq : e+w=3*(m+1) := by
    apply add_right_cancel (b := (9*w))
    calc
      e+w+9*w=e+10*w := by ring
      _=3*n := het
      _=3*(m+1)+9*w := by rw [←hm]; ring
  have hr' : r≤(m+3*w+1)+w := by rw [hm]; exact hr
  have hsize' : 2*w*((m+3*w+1)+w)+5*w≤((67:V)*8807)*e := by
    rw [hm]
    exact hsize
  have hny' : 2*ycoord (m+3*w+1) (2*(firstParam p v-1)+1)=k v := by
    rw [hm]
    exact hny
  exact fixed_graph_variable_width_impossible p v m w r e hp0 hv hz hr' heq hsize' hny' hc

#print axioms Trace74VariableWidthIndexClient.graph_index_impossible
#print axioms Trace74VariableWidthIndexClient.fixed_graph_index_impossible
end Trace74VariableWidthIndexClient
