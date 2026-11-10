import DiophantineConsistency.BFS943.Direct80Fold

/-! Derive the main norm after noncircular graph-specific folding. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80MainNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence TenPositive80Graph TenPositive80Factors TenPositive80Fold
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_main_norm (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ r j d I : V, 0<r ∧ r<j ∧ r%2=1 ∧ 0<j ∧ 0<d ∧ 0<I ∧
      d=xcoord r (A p v-1) ∧ c p v=ycoord r (A p v-1) ∧
      d*d=1+delta p v*(c p v)*(c p v) ∧
      xcoord j (A p v-1)=1+2*(delta p v*U p v*U p v*E p v) ∧
      ycoord j (A p v-1)=I ∧ c p v*c p v∣I := by
  obtain ⟨r,j,I,hr,hrj,hodd,hj,hI,hc,hjx,hjy,hdiv⟩ := graph_odd_ordinate p v hb hv hz
  let A0 : V := A p v
  have hApos : 0<A0 := by
    have hDpos := (factors_positive p v hb hv).1
    exact pos_of_mul_pos_left (by change 0<A0*(A0+2) at hDpos; exact hDpos) (by simp)
  have hA1 : A0-1+1=A0 := tsub_add_cancel_of_le (pos_iff_one_le.mp hApos)
  have hd : ArithmeticPellRecurrence.delta (A0-1)=delta p v := by
    unfold ArithmeticPellRecurrence.delta
    have h3 : A0-1+3=(A0-1+1)+2 := by ring
    rw [h3,hA1]
    rfl
  have hnorm : xcoord r (A0-1)*xcoord r (A0-1)=1+delta p v*(c p v)*(c p v) := by
    have hh := norm r (A0-1)
    rwa [hd,←hc] at hh
  have hx : 0<xcoord r (A0-1) := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x r (A0-1))
  exact ⟨r,j,xcoord r (A0-1),I,hr,hrj,hodd,hj,hx,hI,rfl,hc,hnorm,hjx,hjy,hdiv⟩

#print axioms TenPositive80MainNorm.graph_main_norm
end TenPositive80MainNorm
