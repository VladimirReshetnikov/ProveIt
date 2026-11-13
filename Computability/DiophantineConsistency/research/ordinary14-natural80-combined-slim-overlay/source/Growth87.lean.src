import Divides3X87
import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Source-only direct 87 growth replay. A beta≥46 bound is explicit; no
FreeJ/84 zero, q|X, power equality or endpoint is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Growth87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticPellRecurrence ArithmeticPellPowerRecovery
open NaturalRank84Draft MainBalance87Draft StrongNorm87Draft FirstFields86Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Direct-87 factor-three divisibility and beta≥46 give the X≥16 threshold. -/
theorem X_lower (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    16≤X v := by
  have hj : 1≤v 0 := pos_iff_one_le.mp (hv 0)
  have hq47 : (47:V)≤q beta v := calc
    47=1+46 := by ring
    _≤1+v 0*beta := add_le_add (le_refl 1)
      (le_trans hbeta46 (le_mul_of_one_le_left (Arithmetic.zero_le beta) hj))
    _=q beta v := rfl
  have hdiv := Divides3X87Draft.divides_three_X p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  have hqX : q beta v≤3*X v := Arithmetic.le_of_dvd (mul_pos (by simp) (hv 6)) hdiv
  have h47 : (47:V)≤3*X v := le_trans hq47 hqX
  by_contra hn
  have hx : X v≤15 := lt_succ_iff_le.mp (by
    simpa only [show (15:V)+1=16 by ring] using lt_of_not_ge hn)
  have h3 : 3*X v≤45 := by
    simpa only [show (3:V)*15=45 by ring] using mul_le_mul_of_nonneg_left hx (by simp : (0:V)≤3)
  exact (not_le_of_gt (by norm_num : (45:V)<47)) (le_trans h47 h3)

/-- Direct-87 own-zero growth Exp.exp R<Y. Exact indices, factor-three
projection and beta≥46 are used; no q-divisibility of X is assumed. -/
theorem growth (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    Exp.exp (naturalRank beta MC MF v)<Y v := by
  let xx := X v
  let yy := Y v
  let kk := k v
  let cc := c v
  let aa := a v
  let R := naturalRank beta MC MF v
  have hX : 16≤xx := X_lower p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz
  have hq : 0<q beta v := by dsimp [q]; simp
  have hY : 0<yy := hv 7
  obtain ⟨n,m,d,s,hn13,_,hmR,hnR,hny,_,_,hy,_⟩ :=
    P72ExactIndices87Draft.exact_indices p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz
  let r : V := n-1
  have hn1 : 1≤n := by nlinarith
  have hrplus : r+1=n := tsub_add_cancel_of_le hn1
  have hr2 : 2≤r := by have h := hn13; nlinarith
  have hR : R=2*r+1 := by rw [←hrplus] at hnR; nlinarith
  have hbase : aa=yy*(xx+1) := by dsimp [aa,a]; ring
  have hc : cc=ycoord (2*r+1) (yy*(xx+1)) := by
    rw [←hR,←hmR,←hbase]
    exact hy.symm
  have hk : kk=2*ycoord (r+1) (2*(xx*yy*yy-1)+1) := by
    rw [hrplus]
    exact hny.symm
  have hg := power_bound xx yy r kk cc (v 9) (v 10) hX (pos_iff_one_le.mp hY) hr2
    (by dsimp [cc,c,kk,k]; ring) rfl (hv 10) hc hk
  change Exp.exp R<yy
  rw [hR]
  exact hg

end DiophantineConsistency.Growth87Draft

#print axioms DiophantineConsistency.Growth87Draft.X_lower
#print axioms DiophantineConsistency.Growth87Draft.growth
