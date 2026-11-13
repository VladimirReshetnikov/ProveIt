import FirstIndexModQ487
import RankWindow87

/-! Source-only 87 P72 first-input bundle; no exact-index theorem or Lean
elaboration is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P72FirstInputs87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPellRecurrence
open FirstFields86Draft NaturalRank84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Bundle first-index witnesses, rank bounds, and the strict remainder. -/
theorem first_inputs (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    let qq := q beta v
    let R := naturalRank beta MC MF v
    let m := (v 6*v 7)*v 7
    26≤R ∧ R+1<qq^4 ∧
      ∃ s tau n r w : V, 0<s ∧ v 7=Q beta v*s ∧ 0<tau ∧
        n≤k v ∧ xcoord n (2*(m-1)+1)=tau ∧
        2*ycoord n (2*(m-1)+1)=k v ∧ tau=1+2*m*r ∧ k v=2*n+4*m*w ∧
        (2*n)%(qq^4)=R+1 := by
  let qq := q beta v
  let R := naturalRank beta MC MF v
  have hw := RankWindow87Draft.rank_window p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  have h26 : 26≤R := le_trans (by norm_num : (26:V)≤40) hw.1
  have hlt : R+1<qq^4 := hw.2.2
  obtain ⟨s,tau,n,r,w,hs,hY,ht,hn,hx,hy,hr,hk,hmod⟩ :=
    FirstIndexModQ487Draft.first_index_mod_q4 p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz
  have hmod' : (2*n)%(qq^4)=R+1 := by
    rw [mod_eq_self_of_lt hlt] at hmod
    exact hmod
  exact ⟨h26,hlt,s,tau,n,r,w,hs,hY,ht,hn,hx,hy,hr,hk,hmod'⟩

end DiophantineConsistency.P72FirstInputs87Draft

#print axioms DiophantineConsistency.P72FirstInputs87Draft.first_inputs
