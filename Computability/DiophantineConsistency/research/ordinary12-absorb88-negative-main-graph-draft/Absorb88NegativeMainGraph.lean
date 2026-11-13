import Absorb88NegativeMainOrientation
import Absorb88NegativeRankBound
import Absorb88GraphGap

/-! Draft: orient the actual 88 main root on the negative transport branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88NegativeMainGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open Absorb88NegativeMainOrientation Absorb88NegativeRankBound Absorb88GraphGap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_main_positive (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let P : V := (X*Y)*Y
    let k : V := v 8+v 9
    let a : V := X*Y+Y
    let W : V := Y*(q*q)
    let H : V := 3+4*a
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    let G : DiffRing V := ι (v 2)+(ι b)*(ι q-ι (v 1))
    let rank : DiffRing V := ((ι q)*(ι q)-1)*G+ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q)
    (ι Bp : DiffRing V)<ι Bn →
      0<(ι W : DiffRing V)*(ι X+ι a*(ι (v 8)+ι Y*ι k))+
        ι H*(ι W*ι (v 11)-ι k+rank+1) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let E : V := X*Y
  let P : V := E*Y
  let k : V := v 8+v 9
  let a : V := E+Y
  let W : V := Y*(q*q)
  let H : V := 3+4*a
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let G : DiffRing V := ι (v 2)+(ι b)*(ι q-ι (v 1))
  let rank : DiffRing V := ((ι q)*(ι q)-1)*G+ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q)
  change (ι Bp : DiffRing V)<ι Bn →
      0<(ι W : DiffRing V)*(ι X+ι a*(ι (v 8)+ι Y*ι k))+
        ι H*(ι W*ι (v 11)-ι k+rank+1)
  intro hn
  have hB : (0:DiffRing V)<ι b := by
    rw [←map_zero ι,ι_lt_ι]; exact mul_pos (hv 0) hb
  have hB1 : (1:DiffRing V)≤ι b := one_le_of_pos (fun _ h => pos_iff_one_le.mp h) hB
  have hqeq : (ι q : DiffRing V)=1+ι b := by simp only [q,map_add,map_one]
  have hq2 : (2:DiffRing V)≤ι q := by rw [hqeq]; linarith
  have hs1 : (1:DiffRing V)≤ι (v 6) := by
    apply one_le_of_pos (fun _ h => pos_iff_one_le.mp h)
    rw [←map_zero ι,ι_lt_ι]; exact hv 6
  have hqSq : (4:DiffRing V)≤ι q*ι q := by nlinarith [sq_nonneg ((ι q : DiffRing V)-2)]
  have hqCube : (8:DiffRing V)≤ι q*(ι q*ι q) := by
    have hm := mul_nonneg (show (0:DiffRing V)≤ι q-2 by linarith)
      (show (0:DiffRing V)≤ι q*ι q-4 by linarith)
    nlinarith
  have hYeq : (ι Y : DiffRing V)=ι q*(ι q*ι q)*ι (v 6) := by simp only [Y,map_mul]
  have hY8 : (8:DiffRing V)≤ι Y := by
    have hm := mul_nonneg (show (0:DiffRing V)≤ι q*(ι q*ι q) by positivity)
      (show (0:DiffRing V)≤ι (v 6)-1 by linarith)
    rw [hYeq]; nlinarith
  have hW8 : (8:DiffRing V)≤ι W := by
    have hm := mul_nonneg (show (0:DiffRing V)≤ι Y by exact ι_nonneg _)
      (show (0:DiffRing V)≤ι q*ι q-1 by linarith)
    simp only [W,map_mul]; nlinarith
  have hW : (0:DiffRing V)<ι W := by linarith
  have hE : (0:DiffRing V)<ι E := by
    rw [←map_zero ι,ι_lt_ι]
    have hq : 0<q := by dsimp [q]; simp
    exact mul_pos (mul_pos hq (hv 5)) (mul_pos (mul_pos hq (mul_pos hq hq)) (hv 6))
  have ha : (1:DiffRing V)≤ι a := by
    have hE0 : (0:DiffRing V)≤ι E := hE.le
    simp only [a,map_add]; linarith
  have hH : (0:DiffRing V)<ι H := by
    simp only [H,map_add,map_mul,map_ofNat]; linarith
  have hH7 : (ι H : DiffRing V)≤7*ι a := by
    simp only [H,map_add,map_mul,map_ofNat]; linarith
  have hgap : (0:DiffRing V)≤ι W*ι Y-7-ι W := by
    have hm := mul_nonneg (show (0:DiffRing V)≤ι W by linarith)
      (show (0:DiffRing V)≤ι Y-2 by linarith)
    nlinarith
  have hPE : (ι E : DiffRing V)≤ι P := by
    have hm := mul_nonneg hE.le (show (0:DiffRing V)≤ι Y-1 by linarith)
    simp only [P,map_mul]; nlinarith
  have hk : (8:DiffRing V)*ι E≤ι k := by
    have hh := graph_gap p v hb hv hz
    change 8*P+4≤k at hh
    have hh' := ι_le_ι.mpr hh
    simp only [map_add,map_mul,map_ofNat] at hh'
    nlinarith
  have hqp : ((ι q : DiffRing V)*ι q)*ι P=ι W*ι E := by
    simp only [P,W,E,map_mul]; ring
  have hrank := graph_rank_lower p v hb hv hz hn
  change -(ι q : DiffRing V)*ι q*ι P≤rank at hrank
  have hrank' : -((ι q : DiffRing V)*ι q*ι P)≤rank := by nlinarith
  exact main_positive (ι X) (ι Y) (ι E) (ι P) ((ι q)*ι q) (ι W) (ι a) (ι H)
    (ι (v 8)) (ι k) (ι (v 11)) rank
    (ι_nonneg _) (ι_nonneg _) hE hW (lt_of_lt_of_le (by norm_num) ha) hH
    (ι_nonneg _) (ι_nonneg _) hgap hk hH7 hqp hrank'

#print axioms Absorb88NegativeMainGraph.graph_main_positive
end Absorb88NegativeMainGraph
