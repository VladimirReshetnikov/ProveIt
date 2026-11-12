import MainBalance85
import ShiftedGuardFacts

/-! Source-only q⁴ rank congruence from the 85 own-zero balance. The old
X*Y*q term is retained; no 84/FreeJ zero or q|X is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Q4Rank85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open NaturalRank84Draft DirectNorms85Draft ShiftedGuardFacts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Direct 85 main balance yields q⁴ dividing the magnitude of R+1−k.
The factor-three argument does not require q coprime to 3. -/
theorem q4_rank (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)
    (hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    (q beta v)^4∣magnitude (naturalRank beta MC MF v+1,k v) := by
  let qq := q beta v
  let xx := X v
  let yy := Y beta v
  let uu := U beta v
  let aa := a beta v
  let cc := c beta v
  let kk := k v
  let R := naturalRank beta MC MF v
  let H : V := 3+4*yy*(xx+1)
  have hq : 0<qq := by dsimp [qq,q]; simp
  have hY : qq^3∣yy := by
    refine ⟨v 7,?_⟩
    dsimp [yy,Y]
    ring
  have hU : uu=qq^5*v 7 := by
    dsimp [uu,yy,U,Y]
    ring
  obtain ⟨d,_,hbal⟩ := MainBalance85Draft.norm_and_balance p beta K MC MF v
    hbeta hport hK hMC hMF hv hz
  have hH : H=3+4*aa := by dsimp [H,aa,a]; ring
  have hb : H*(xx*yy*qq+(R+1))+qq^5*(v 7*(xx+aa*cc+H*v 12)) =
      H*kk+qq^5*(v 7*d) := by
    calc
      _=uu*(xx+aa*cc)+H*(uu*v 12+xx*yy*qq+R+1) := by rw [hU]; ring
      _=uu*d+H*kk := by simpa only [hH] using hbal.symm
      _=H*kk+qq^5*(v 7*d) := by rw [hU]; ring
  exact q4_rank_from_balance qq yy xx R kk (v 7*(xx+aa*cc+H*v 12)) (v 7*d)
    hq hY hb

end DiophantineConsistency.Q4Rank85Draft

#print axioms DiophantineConsistency.Q4Rank85Draft.q4_rank
