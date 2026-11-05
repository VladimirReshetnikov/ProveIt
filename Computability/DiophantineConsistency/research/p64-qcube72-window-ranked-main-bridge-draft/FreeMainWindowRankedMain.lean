import FreeMainActualRankWindowGeneric
import FreeMainRankHalf
import FreeMainRankedMain

/-! Unchecked draft: main Pell coordinates at actual rank, under the two mask
inequalities. This is not a reverse witness map. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainWindowRankedMain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence FreeMainConditionalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_at_rank (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀ i, 0<v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)
    (hq : 33≤qval p v)
    (hMC : (p 2:V)<(p 0:V)) (hMF : (p 3:V)<2*(p 0:V)) :
    ∃ g : V, g*g=1+delta (aval p v)*(cval p v)*(cval p v) ∧
      xcoord (FreeMainAuxNorm.rank p v) (aval p v)=g ∧
      ycoord (FreeMainAuxNorm.rank p v) (aval p v)=cval p v := by
  let q : V := qval p v
  let Y : V := yval p v
  let X : V := v 8*q
  let a : V := aval p v
  let c : V := cval p v
  let R : V := FreeMainAuxNorm.rank p v
  have hw := FreeMainActualRankWindowGeneric.actual_window p v hv hz hMC hMF
  change 0<R ∧ (ι R:DiffRing V)+1 < (ι q)*(ι q*((ι q)*(ι q))) at hw
  obtain ⟨g,m,hg,_,_,_⟩ := FreeMainGraphMainRoot.main_index p v hv hz
  change g*g=1+delta a*c*c at hg
  let Q : DiffRing V := ι q
  let YY : DiffRing V := ι Y
  let XX : DiffRing V := ι X
  let CC : DiffRing V := ι c
  let GG : DiffRing V := ι g
  let RR : DiffRing V := ι R
  have hQ : 0≤Q := ι_nonneg q
  have hq1 : 1≤Q := by
    have hh : (1:V)≤q := by dsimp [q,qval]; simp
    exact (ι_le_ι (V:=V)).mpr hh
  have hw1 : (1:DiffRing V)≤ι (v 8) := by
    simpa using (ι_le_ι (V:=V)).mpr (pos_iff_one_le.mp (hv 8))
  have hs1 : (1:DiffRing V)≤ι (v 7) := by
    simpa using (ι_le_ι (V:=V)).mpr (pos_iff_one_le.mp (hv 7))
  have ht1 : (1:DiffRing V)≤ι (v 10) := by
    simpa using (ι_le_ι (V:=V)).mpr (pos_iff_one_le.mp (hv 10))
  have hu1 : (1:DiffRing V)≤ι (v 11) := by
    simpa using (ι_le_ι (V:=V)).mpr (pos_iff_one_le.mp (hv 11))
  have hX : Q≤XX := by
    have hh := mul_le_mul_of_nonneg_right hw1 hQ
    simpa [XX,X,Q,map_mul] using hh
  have hQ3 : 0≤Q*Q*Q := mul_nonneg (mul_nonneg hQ hQ) hQ
  have hY : Q*Q*Q≤YY := by
    have hh := mul_le_mul_of_nonneg_left hs1 hQ3
    simpa [YY,Y,yval,Q,q,map_mul] using hh
  have hY1 : 1≤YY := by
    have hqq : 1≤Q*Q := by nlinarith
    have hqqq : 1≤Q*Q*Q := by
      nlinarith [mul_nonneg (show 0≤Q-1 by linarith) (show 0≤Q*Q-1 by linarith)]
    exact le_trans hqqq hY
  have hcshape : CC=((ι (v 10):DiffRing V)+ι (v 11))*YY+ι (v 10) := by
    change (ι ((v 10+v 11)*Y+v 10):DiffRing V)=_
    simp only [map_add,map_mul,YY]
  have hc3 : 3≤CC := by
    have hm := mul_nonneg (show 0≤(ι (v 10):DiffRing V)+(ι (v 11))-2 by linarith)
      (show 0≤YY-1 by linarith)
    rw [hcshape]
    nlinarith
  have ha : (ι a:DiffRing V)=XX*YY+YY := by
    simp [a,aval,X,Y,yval,XX,YY,q,map_add,map_mul]
  have hd : (ι (delta a):DiffRing V)=
      ((XX*YY+YY)+2)*((XX*YY+YY)+2)-1 := by
    simp only [delta,map_add,map_mul,map_one,map_ofNat]
    rw [ha]
    ring
  have hpell : GG*GG=1+(((XX*YY+YY)+2)*((XX*YY+YY)+2)-1)*(CC*CC) := by
    have hh := congrArg (fun x : V => (ι x:DiffRing V)) hg
    simp only [map_add,map_mul,map_one] at hh
    rw [hd] at hh
    dsimp [GG,CC]
    nlinarith [hh]
  have hwin : RR+1<Q*(Q*Q*Q) := by
    dsimp [RR,Q]
    simpa only [mul_assoc] using hw.2
  have hhalfR := FreeMainRankHalf.rank_half Q XX YY RR CC GG hQ hX hY hwin hc3
    (ι_nonneg g) hpell
  have hhalf : 2*R<c := by
    apply (ι_lt_ι (V:=V)).mp
    simpa [RR,CC,map_mul,map_ofNat] using hhalfR
  exact FreeMainRankedMain.main_at_rank p v hv hz hq hw.1 hhalf

#print axioms FreeMainWindowRankedMain.main_at_rank
end FreeMainWindowRankedMain
