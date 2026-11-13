import MainBalance87
import QCubeSize87
import ShiftedGuardFacts

/-! Source-only q⁴ rank congruence from the 87 own-zero balance. The old
X*Y*q term is retained; no 84/FreeJ zero or q|X is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Q4Rank87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open NaturalRank84Draft MainBalance87Draft StrongNorm87Draft FirstFields86Draft ShiftedGuardFacts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Direct 87 main balance yields q⁴ dividing the magnitude of R+1−k.
The factor-three argument does not require q coprime to 3. -/
theorem q4_rank (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)
    (hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    (q beta v)^4∣magnitude (naturalRank beta MC MF v+1,k v) := by
  let qq := q beta v
  let xx := X v
  let yy := Y v
  let uu := U beta v
  let aa := a v
  let cc := c v
  let kk := k v
  let R := naturalRank beta MC MF v
  let H : V := 3+4*yy*(xx+1)
  have hq : 0<qq := by dsimp [qq,q]; simp
  obtain ⟨s,tau,hs,hYs,_,_⟩ := FirstQuotient87Draft.quotient_and_root
    p beta v hbeta (hv 0) (hv 7) hport hz
  have hY : qq^3∣yy := by
    refine ⟨s,?_⟩
    calc
      yy=Q beta v*s := hYs
      _=qq^3*s := by dsimp [Q,qq]; ring
  have hU : uu=qq^5*s := by
    dsimp [uu,yy,U,Y,qq] at hYs ⊢
    rw [hYs]
    dsimp [Q]
    ring
  have hY8 : 8≤Y v := QCubeSize87Draft.Y_at_least_eight p beta v hbeta (hv 0) (hv 7) hport hz
  obtain ⟨d,_,hbal⟩ := MainBalance87Draft.norm_and_balance p beta K MC MF v
    hbeta hport hK hMC hMF hv hY8 hz
  have hH : H=3+4*aa := by dsimp [H,aa,a]; ring
  have hb : H*(xx*yy*qq+(R+1))+qq^5*(s*(xx+aa*cc+H*v 12)) =
      H*kk+qq^5*(s*d) := by
    calc
      _=uu*(xx+aa*cc)+H*(uu*v 12+xx*yy*qq+R+1) := by rw [hU]; ring
      _=uu*d+H*kk := by simpa only [hH] using hbal.symm
      _=H*kk+qq^5*(s*d) := by rw [hU]; ring
  exact q4_rank_from_balance qq yy xx R kk (s*(xx+aa*cc+H*v 12)) (s*d)
    hq hY hb

end DiophantineConsistency.Q4Rank87Draft

#print axioms DiophantineConsistency.Q4Rank87Draft.q4_rank
