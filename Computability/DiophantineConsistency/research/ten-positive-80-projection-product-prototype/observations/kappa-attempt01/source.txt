import Direct80GraphUnweighted

/-! Positive integral projection quotient for the 80 graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80Kappa
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalProjection
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_positive_kappa (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) :
    ∃ kappa : V, 0<kappa ∧ Knat p v=Hnat p v*kappa := by
  obtain ⟨kappa,hkappa⟩ := Direct80GraphUnweighted.graph_unweighted p v hbeta31 hl hh hv hz hbetaodd
  have hK : 0<Knat p v := by dsimp [Knat]; simp
  have hk : 0<kappa := pos_of_mul_pos_right (by rw [←hkappa]; exact hK) (by simp)
  exact ⟨kappa,hk,hkappa⟩

#print axioms Direct80Kappa.graph_positive_kappa
end Direct80Kappa
