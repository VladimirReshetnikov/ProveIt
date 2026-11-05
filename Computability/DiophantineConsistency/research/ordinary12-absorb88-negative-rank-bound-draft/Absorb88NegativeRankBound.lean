import Absorb88NegativeTransportGraph

/-! Draft: signed-rank lower bound on the negative transport branch. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88NegativeRankBound

theorem rank_lower {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (b q F alpha A P U RJ : R)
    (hb : 0<b) (hq : q=b+1) (hF : 0<F) (ha : 0<alpha) (hA : 1≤A)
    (hP : 0≤P) (hRJ : 0≤RJ)
    (hU : U=q*((F+alpha-q)*A+F)) (hUP : U≤P) :
    -(q*q)*P ≤ (q*q-1)*(alpha+b*(q-F))+RJ := by
  have hqpos : 0<q := by linarith
  have hqq : 0≤q*q-1 := by nlinarith [sq_nonneg (q-1)]
  have hGP : 0≤alpha+b*(q-F)+P := by
    by_cases hG : 0≤alpha+b*(q-F)
    · linarith
    · have hGneg : alpha+b*(q-F)<0 := lt_of_not_ge hG
      have hFq : q<F := by
        by_contra hn
        have hm := mul_nonneg hb.le (sub_nonneg.mpr (le_of_not_gt hn))
        linarith
      have hD : 0<F+alpha-q := by linarith
      have hApos : 0<A := by linarith
      have hm := mul_pos hqpos (mul_pos hD hApos)
      have hqF : q*F<U := by rw [hU]; nlinarith
      have hbF : b*F<q*F := by rw [hq]; nlinarith
      have hbq : 0<b*q := mul_pos hb hqpos
      nlinarith
  have hm := mul_nonneg hqq hGP
  nlinarith

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open Absorb88NegativeTransportGraph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_rank_lower (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let P : V := (X*Y)*Y
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    (ι Bp : DiffRing V) < ι Bn →
      -(ι q : DiffRing V)*(ι q)*(ι P) ≤
        ((ι q : DiffRing V)*(ι q)-1)*(ι (v 2)+(ι b)*(ι q-ι (v 1)))+
          ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q) := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let P : V := (X*Y)*Y
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  change (ι Bp : DiffRing V) < ι Bn →
      -(ι q : DiffRing V)*(ι q)*(ι P) ≤
        ((ι q : DiffRing V)*(ι q)-1)*(ι (v 2)+(ι b)*(ι q-ι (v 1)))+
          ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q)
  intro hn
  have hb0 : 0<b := mul_pos (hv 0) hb
  have hB : (0:DiffRing V)<ι b := by rw [← map_zero ι,ι_lt_ι]; exact hb0
  have hF : (0:DiffRing V)<ι (v 1) := by rw [← map_zero ι,ι_lt_ι]; exact hv 1
  have ha : (0:DiffRing V)<ι (v 2) := by rw [← map_zero ι,ι_lt_ι]; exact hv 2
  have hA : (1:DiffRing V)≤ι A := by
    apply one_le_of_pos (fun _ h => pos_iff_one_le.mp h)
    rw [← map_zero ι,ι_lt_ι]
    exact add_pos_of_nonneg_of_pos (by simp) (hv 5)
  have hq : (ι q : DiffRing V)=ι b+1 := by simp only [q,map_add,map_one,add_comm]
  have hRJ : (0:DiffRing V)≤ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q) :=
    mul_nonneg (ι_nonneg _) (add_nonneg (ι_nonneg _) (mul_nonneg (ι_nonneg _) (ι_nonneg _)))
  have hshape : (ι q : DiffRing V)*(ι Bn-ι Bp)=
      ι q*((ι (v 1)+ι (v 2)-ι q)*ι A+ι (v 1)) := by
    dsimp only [Bn,Bp]; simp only [map_add,map_mul]; ring
  have hUP := graph_negative_transport_bound p v hb hv hz hn
  have hresult := rank_lower (ι b) (ι q) (ι (v 1)) (ι (v 2)) (ι A) (ι P)
    ((ι q)*(ι Bn-ι Bp)) (ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q))
    hB hq hF ha hA (ι_nonneg _) hRJ hshape hUP
  nlinarith [hresult]

#print axioms Absorb88NegativeRankBound.rank_lower
#print axioms Absorb88NegativeRankBound.graph_rank_lower
end Absorb88NegativeRankBound
