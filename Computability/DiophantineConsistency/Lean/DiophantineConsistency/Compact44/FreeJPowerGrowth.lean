import DiophantineConsistency.Compact44.FreeJPowerProjection
import DiophantineConsistency.ArithmeticPellPowerRecovery
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJPowerGrowth
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.Ordinary12FreeJ
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellPowerRecovery
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem X_lower (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) : 16≤v 5 := by
  have hj : (1:V)≤v 0 := pos_iff_one_le.mp (hv 0)
  have hq : (47:V)≤1+v 0*(p 0:V) := calc
    47=1+46 := by ring
    _≤1+v 0*(p 0:V) := _root_.add_le_add (le_refl 1)
      (le_trans hbeta (le_mul_of_one_le_left (by simp) hj))
  have hp : 1+v 0*(p 0:V)≤3*v 5 := (FreeJPowerProjection.graph_projection p v hb hl hh hv hz).2
  have hp' : (47:V)≤3*v 5 := le_trans hq hp
  by_contra hn
  have hx : v 5≤15 := lt_succ_iff_le.mp (by
    simpa only [show (15:V)+1=16 by ring] using lt_of_not_ge hn)
  have h3 : 3*v 5≤45 := by
    simpa only [show (3:V)*15=45 by ring] using mul_le_mul_of_nonneg_left hx (by simp : (0:V)≤3)
  exact (not_le_of_gt (by norm_num : (45:V)<47)) (le_trans hp' h3)

theorem growth (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    Exp.exp R<v 6 := by
  let q : V := 1+v 0*(p 0:V)
  let X : V := v 5
  let Y : V := v 6
  let Q : V := X*Y*Y
  let k : V := v 8+v 9
  let c : V := v 8+Y*k
  let a : V := X*Y+Y
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  have hX : 16≤X := X_lower p v hb hl hh hv hz hbeta
  obtain ⟨first,main,n,m,_,_,hn13,_,hmR,hnR,_,hny,_,hmy⟩ :=
    FreeJExactOrdinary.exact_ordinary_indices p v hb hl hh hv hz
  change m=R at hmR
  change 2*n=R+1 at hnR
  let r : V := n-1
  have hn1 : 1≤n := le_trans (by simpa only [show (1:V)+12=13 by ring] using
    (show (1:V)≤1+12 by simp)) hn13
  have hrplus : r+1=n := tsub_add_cancel_of_le hn1
  have hr2 : 2≤r := by
    apply (add_le_add_iff_right (1:V)).mp
    rw [hrplus]
    have h3 : (3:V)≤13 := by simpa only [show (3:V)+10=13 by ring] using (show (3:V)≤3+10 by simp)
    simpa only [show (2:V)+1=3 by ring] using le_trans h3 hn13
  have hR : R=2*r+1 := by
    apply add_right_cancel (b:=(1:V))
    calc
      R+1=2*n := hnR.symm
      _=2*(r+1) := by rw [hrplus]
      _=(2*r+1)+1 := by ring
  have hbase : a=Y*(X+1) := by dsimp [a,X,Y]; ring
  have hc : c=ycoord (2*r+1) (Y*(X+1)) := by
    change ycoord m a=c at hmy
    rw [←hR,←hmR,←hbase]
    exact hmy.symm
  have hk : k=2*ycoord (r+1) (2*(X*Y*Y-1)+1) := by
    change 2*ycoord n (2*(Q-1)+1)=k at hny
    rw [hrplus]
    exact hny.symm
  have hg := power_bound X Y r k c (v 8) (v 9) hX (pos_iff_one_le.mp (hv 6)) hr2
    (by dsimp [c]; ring) rfl (hv 9) hc hk
  change Exp.exp R<Y
  rw [hR]
  exact hg
end FreeJPowerGrowth
#print axioms FreeJPowerGrowth.X_lower
#print axioms FreeJPowerGrowth.growth
