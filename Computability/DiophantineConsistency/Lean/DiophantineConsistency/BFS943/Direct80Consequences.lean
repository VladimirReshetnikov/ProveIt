import DiophantineConsistency.BFS943.Direct80Joined

/-! Direct signed-coordinate consequence; not an all-index fold. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80Consequences
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open TenPositive80Graph TenPositive80Factors TenPositive80Joined
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signed_coordinate (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let A0 := A p v
    let F := 1+2*(D*U0*U0*E0)
    ∃ I j h : V, 0<I ∧ 0<j ∧ c p v≤I ∧
      c p v*c p v∣I ∧ xcoord j (A0-1)=F ∧ ycoord j (A0-1)=I ∧
      SignMod F (c p v) (ycoord (2*h+1) (A0-1)) := by
  let D : V := delta p v
  let U0 : V := U p v
  let E0 : V := E p v
  let A0 : V := A p v
  let F : V := 1+2*(D*U0*U0*E0)
  obtain ⟨tau,f,V0,y,I,j,h,htau,hf,hV,hy,hI,hj,ht,hf2,hIeq,hdiv,hjx,hjy,_hauxx,_hauxy,hgc,hgu⟩ :=
    strong_and_auxiliary_indices_with_graph_residue p v hb hv hz
  have hF : 0<F := by dsimp [F]; simp
  have hcpos : 0<c p v := by
    by_contra hn
    have hc0 : c p v=0 := le_antisymm (le_of_not_gt hn) (by simp)
    rw [hc0] at hdiv
    simp only [zero_mul,zero_dvd_iff] at hdiv
    exact (ne_of_gt hI) hdiv
  have hcle : c p v≤c p v*c p v := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pos_iff_one_le.mp hcpos) (by simp : (0:V)≤c p v)
  have hbound : c p v≤I := le_trans hcle (Arithmetic.le_of_dvd hI hdiv)
  exact ⟨I,j,h,hI,hj,hbound,hdiv,hjx,hjy,sign_trans hF (sign_symm hgc) hgu⟩

#print axioms TenPositive80Consequences.signed_coordinate
end TenPositive80Consequences
