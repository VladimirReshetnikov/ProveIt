import P72ExactIndices85
import DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011

/-! Source-only direct 85 projection replay. No q|X, power equality,
84 zero or FreeJ zero is assumed; draft imports remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Divides3X85Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticAdaptiveFirstDivisibility2011
open NaturalRank84Draft DirectNorms85Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed direct 85 own-zero q∣3X projection, using exact indices and the
old X*Y*q carrier balance, with explicit mask and natural-port hypotheses. -/
theorem divides_three_X (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P85QcubeGraph.graph p).output v) :
    q beta v∣3*X v := by
  let qq := q beta v
  let xx := X v
  let yy := Y beta v
  let uu := U beta v
  let aa := a beta v
  let cc := c beta v
  let kk := k v
  let R := naturalRank beta MC MF v
  let H : V := 3+4*aa
  obtain ⟨n,m,d,s,_,_,_,hnR,_,hks,_,_,hbal⟩ :=
    P72ExactIndices85Draft.exact_indices p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  let W : V := 4*xx*qq*(v 7)*s
  have hk : kk=R+1+uu*W := by
    rw [hks,hnR]
    dsimp [W,uu,yy,U,Y]
    ring
  have hcancel : uu*(d+H*W)=uu*(xx+aa*cc+H*v 12)+H*(xx*yy*qq) := by
    apply add_right_cancel (b:=H*(R+1))
    calc
      uu*(d+H*W)+H*(R+1)=uu*d+H*(R+1+uu*W) := by ring
      _=uu*d+H*kk := by rw [hk]
      _=uu*(xx+aa*cc)+H*(uu*v 12+xx*yy*qq+R+1) := hbal
      _=(uu*(xx+aa*cc+H*v 12)+H*(xx*yy*qq))+H*(R+1) := by ring
  have hq : 0<qq := by dsimp [qq,q]; simp
  have hY : 0<yy := by dsimp [yy,Y]; exact mul_pos (mul_pos hq (mul_pos hq hq)) (hv 7)
  have hqY : 0<qq*yy := mul_pos hq hY
  have hqeq : qq*(d+H*W)=qq*(xx+aa*cc+H*v 12)+H*xx := by
    apply mul_left_cancel₀ (ne_of_gt hqY)
    calc
      (qq*yy)*(qq*(d+H*W))=uu*(d+H*W) := by dsimp [uu,U]; ring
      _=uu*(xx+aa*cc+H*v 12)+H*(xx*yy*qq) := hcancel
      _=(qq*yy)*(qq*(xx+aa*cc+H*v 12)+H*xx) := by dsimp [uu,U]; ring
  let D : V := 4*(qq*qq)*(v 7)*(xx+1)
  have hH : H=3+qq*D := by dsimp [H,aa,a,yy,Y,D]; ring
  have heq : qq*(d+H*W)=3*xx+qq*(xx+aa*cc+H*v 12+D*xx) := calc
    _=qq*(xx+aa*cc+H*v 12)+H*xx := hqeq
    _=3*xx+qq*(xx+aa*cc+H*v 12+D*xx) := by rw [hH]; ring
  apply mod_eq_zero_iff_dvd.mp
  have hm := congrArg (fun z : V => z%qq) heq
  rw [show qq*(d+H*W)=0+qq*(d+H*W) by ring,
    mod_add_mul' _ _ hq,mod_add_mul' _ _ hq,zero_mod] at hm
  exact hm.symm

end DiophantineConsistency.Divides3X85Draft

#print axioms DiophantineConsistency.Divides3X85Draft.divides_three_X
