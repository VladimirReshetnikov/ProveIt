import FirstIndexModQ4
import RankWindow
import RankLower40

/-! Source-only first-index input bundle for the P72 route. Imported drafts
are unelaborated. The strong/auxiliary norms and exact calibration remain. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P72FirstInputs84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticPellRecurrence DirectFirstRootGraphClientDraft NaturalRank84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Bundle the own-zero first Pell index/residue and rank bounds needed by
P72Exact, without asserting the latter theorem's remaining premises. -/
theorem first_inputs (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    let q := AuxGraphNormClientDraft.q beta v
    let R := naturalRank beta MC MF v
    let Q := (X beta v*Y beta v)*Y beta v
    let tau := magnitude (firstP beta v,v 8)
    let kk := k v
    26≤R ∧ R+1<q^4 ∧
      ∃ n r s : V, n≤kk ∧ xcoord n (2*(Q-1)+1)=tau ∧
        2*ycoord n (2*(Q-1)+1)=kk ∧ tau=1+2*Q*r ∧ kk=2*n+4*Q*s ∧
        (2*n)%(q^4)=R+1 := by
  let q := AuxGraphNormClientDraft.q beta v
  let R := naturalRank beta MC MF v
  have hlower : 40≤R := RankLower4084Draft.rank_lower40 p beta K MC MF v hbeta hport hK hv hz
  have h26 : 26≤R := le_trans (by norm_num : (26:V)≤40) hlower
  have hwindow := RankWindow84Draft.rank_window p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  have hlt : R+1<q^4 := hwindow.2.2
  obtain ⟨n,r,s,hn,hx,hy,hr,hk,hmod⟩ :=
    FirstIndexModQ484Draft.first_index_mod_q4 p beta K MC MF v hbeta hport hK hMCcast hMFcast hv hz
  have hmod' : (2*n)%(q^4)=R+1 := by
    rw [mod_eq_self_of_lt hlt] at hmod
    exact hmod
  exact ⟨h26,hlt,n,r,s,hn,hx,hy,hr,hk,hmod'⟩

end DiophantineConsistency.P72FirstInputs84Draft

#print axioms DiophantineConsistency.P72FirstInputs84Draft.first_inputs
