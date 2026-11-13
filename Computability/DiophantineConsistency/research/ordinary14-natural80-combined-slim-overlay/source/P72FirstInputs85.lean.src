import FirstIndexModQ485
import RankWindow85

/-! Source-only first-index input bundle for the P72 route. Imported drafts
are unelaborated. The strong/auxiliary norms and exact calibration remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P72FirstInputs85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticPellRecurrence DirectNorms85Draft NaturalRank84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Bundle the own-zero first Pell index/residue and rank bounds needed by
P72Exact, without asserting the latter theorem's remaining premises. -/
theorem first_inputs (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    let q := DirectNorms85Draft.q beta v
    let R := naturalRank beta MC MF v
    let Q := (X v*Y beta v)*Y beta v
    let tau := magnitude (firstP beta v,v 8)
    let kk := k v
    26≤R ∧ R+1<q^4 ∧
      ∃ n r s : V, n≤kk ∧ xcoord n (2*(Q-1)+1)=tau ∧
        2*ycoord n (2*(Q-1)+1)=kk ∧ tau=1+2*Q*r ∧ kk=2*n+4*Q*s ∧
        (2*n)%(q^4)=R+1 := by
  let q := DirectNorms85Draft.q beta v
  let R := naturalRank beta MC MF v
  have hwindow := RankWindow85Draft.rank_window p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  have hlower : 40≤R := hwindow.1
  have h26 : 26≤R := le_trans (by norm_num : (26:V)≤40) hlower
  have hlt : R+1<q^4 := hwindow.2.2
  obtain ⟨n,r,s,hn,hx,hy,hr,hk,hmod⟩ :=
    FirstIndexModQ485Draft.first_index_mod_q4 p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz
  have hmod' : (2*n)%(q^4)=R+1 := by
    rw [mod_eq_self_of_lt hlt] at hmod
    exact hmod
  exact ⟨h26,hlt,n,r,s,hn,hx,hy,hr,hk,hmod'⟩

end DiophantineConsistency.P72FirstInputs85Draft

#print axioms DiophantineConsistency.P72FirstInputs85Draft.first_inputs
