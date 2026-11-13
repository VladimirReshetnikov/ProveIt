import Growth87
import DiophantineConsistency.Compact44.FreeJPowerFinish

/-! Source-only direct 87 power-recovery replay. The FreeJ source is cited for
arithmetic lemmas, not invoked as a graph theorem. All draft imports remain
unelaborated; no q|X, 84 zero or endpoint is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.PowerRecovery87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPellRecurrence
open ArithmeticPellPowerRecovery ArithmeticPellCongruences ArithmeticAdaptiveFirstDivisibility2011
open NaturalRank84Draft MainBalance87Draft StrongNorm87Draft FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed X=2^R from the direct 87 own-zero, with explicit beta≥46,
port casts and mask bounds. No FreeJ graph-zero theorem is invoked. -/
theorem power (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    X v=Exp.exp (naturalRank beta MC MF v) := by
  let qq := q beta v
  let xx := X v
  let yy := Y v
  let uu := U beta v
  let aa := a v
  let cc := c v
  let kk := k v
  let R := naturalRank beta MC MF v
  let H : V := 3+4*aa
  obtain ⟨n,m,main,s,_,_,hmR,hnR,_,hks,hmx,hmy,hbal⟩ :=
    P72ExactIndices87Draft.exact_indices p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  obtain ⟨s0,tau,hs0,hYs,_,_⟩ := FirstQuotient87Draft.quotient_and_root
    p beta v hbeta (hv 0) (hv 7) hport hz
  let W : V := 4*xx*qq*s0*s
  have hk : kk=R+1+uu*W := by
    rw [hks,hnR]
    dsimp [W,uu,yy,U,Y]
    rw [hYs]
    dsimp [Q]
    ring
  have hcancel : uu*(main+H*W)=uu*(xx+aa*cc+H*v 12)+H*(xx*yy*qq) := by
    apply add_right_cancel (b:=H*(R+1))
    calc
      uu*(main+H*W)+H*(R+1)=uu*main+H*(R+1+uu*W) := by ring
      _=uu*main+H*kk := by rw [hk]
      _=uu*(xx+aa*cc)+H*(uu*v 12+xx*yy*qq+R+1) := hbal
      _=(uu*(xx+aa*cc+H*v 12)+H*(xx*yy*qq))+H*(R+1) := by ring
  have hq : 0<qq := by dsimp [qq,q]; simp
  have hY : 0<yy := hv 7
  have hqY : 0<qq*yy := mul_pos hq hY
  have hqeq : qq*(main+H*W)=qq*(xx+aa*cc+H*v 12)+H*xx := by
    apply mul_left_cancel₀ (ne_of_gt hqY)
    calc
      (qq*yy)*(qq*(main+H*W))=uu*(main+H*W) := by dsimp [uu,U]; ring
      _=uu*(xx+aa*cc+H*v 12)+H*(xx*yy*qq) := hcancel
      _=(qq*yy)*(qq*(xx+aa*cc+H*v 12)+H*xx) := by dsimp [uu,U]; ring
  let D : V := 4*(qq*qq)*s0*(xx+1)
  have hH : H=3+qq*D := by
    dsimp [H,aa,a,yy,Y,D,qq]
    rw [hYs]
    dsimp [Q]
    ring
  have hm : (qq*D)*(main+H*W)=(qq*D)*(xx+aa*cc+H*v 12)+H*D*xx := calc
    _=D*(qq*(main+H*W)) := by ring
    _=D*(qq*(xx+aa*cc+H*v 12)+H*xx) := by rw [hqeq]
    _=_ := by ring
  have hcross : H*(main+H*W)+3*(xx+aa*cc+H*v 12) =
      3*(main+H*W)+H*(xx+aa*cc+H*v 12)+H*D*xx := calc
    _=3*(main+H*W)+(qq*D)*(main+H*W)+3*(xx+aa*cc+H*v 12) := by rw [hH]; ring
    _=3*(main+H*W)+((qq*D)*(xx+aa*cc+H*v 12)+H*D*xx)+3*(xx+aa*cc+H*v 12) := by rw [hm]
    _=_ := by rw [hH]; ring
  have hcross' : 3*(xx+aa*cc)+H*(main+H*W+3*v 12) =
      3*main+H*(3*W+xx+aa*cc+H*v 12+D*xx) := by
    calc
      _=H*(main+H*W)+3*(xx+aa*cc+H*v 12) := by ring
      _=3*(main+H*W)+H*(xx+aa*cc+H*v 12)+H*D*xx := hcross
      _=_ := by ring
  have hHp : 0<H := by dsimp [H]; simp
  have hmod : (3*(xx+aa*cc))%H=(3*main)%H := by
    have h := congrArg (fun z : V => z%H) hcross'
    rw [mod_add_mul' _ _ hHp,mod_add_mul' _ _ hHp] at h
    exact h
  have hxR : xcoord R aa=main := by rw [←hmR]; exact hmx
  have hyR : ycoord R aa=cc := by rw [←hmR]; exact hmy
  obtain ⟨w,hw⟩ := projection_quotient aa R
  have hproj : main=Exp.exp R+aa*cc+(4*aa+3)*w := by rw [←hxR,←hyR]; exact hw
  have hHform : H=4*aa+3 := by dsimp [H]; ring
  have hproj' : main=Exp.exp R+aa*cc+H*w := by rw [hHform]; exact hproj
  have hres : (3*xx+3*aa*cc)%H=(3*Exp.exp R+3*aa*cc)%H := calc
    _=(3*(xx+aa*cc))%H := by congr 1; ring
    _=(3*main)%H := hmod
    _=(3*Exp.exp R+3*aa*cc+H*(3*w))%H := by rw [hproj']; congr 1; ring
    _=(3*Exp.exp R+3*aa*cc)%H := mod_add_mul' _ _ hHp
  have h3mod : (3*xx)%H=(3*Exp.exp R)%H := mod_cancel hHp hres
  have hY1 : 1≤yy := pos_iff_one_le.mp hY
  have hXa : xx<aa := by
    have ha : xx+1≤aa := calc
      xx+1≤yy*(xx+1) := le_mul_of_one_le_left (by simp) hY1
      _=aa := by dsimp [aa,a]; ring
    exact lt_of_lt_of_le (lt_add_one xx) ha
  have hYa : yy≤aa := calc
    yy≤yy*(xx+1) := le_mul_of_one_le_right (by simp) (by simp)
    _=aa := by dsimp [aa,a]; ring
  have h3a : 3*aa<H := calc
    3*aa<3*aa+(aa+3) := lt_add_of_pos_right _ (by simp)
    _=H := by dsimp [H]; ring
  have h3X : 3*xx<H := lt_trans (mul_lt_mul_of_pos_left hXa (by simp)) h3a
  have hg : Exp.exp R<yy := Growth87Draft.growth p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz
  have h3exp : 3*Exp.exp R<H :=
    lt_trans (mul_lt_mul_of_pos_left (lt_of_lt_of_le hg hYa) (by simp)) h3a
  rw [mod_eq_self_of_lt h3X,mod_eq_self_of_lt h3exp] at h3mod
  change xx=Exp.exp R
  exact mul_left_cancel₀ (by simp : (3:V)≠0) h3mod

end DiophantineConsistency.PowerRecovery87Draft

#print axioms DiophantineConsistency.PowerRecovery87Draft.power
