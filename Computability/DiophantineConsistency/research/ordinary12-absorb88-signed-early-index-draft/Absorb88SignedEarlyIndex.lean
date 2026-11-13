import Absorb88SignedRankCongruence
import Absorb88GraphGap

/-! Draft: bind the signed rank congruence to the first Pell index. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88SignedEarlyIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellFirstNorm
open Absorb88FirstQuotient Absorb88GraphGap Absorb88SignedRankCongruence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_signed_early (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let P : V := (X*Y)*Y
    let k : V := v 8+v 9
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    let G : DiffRing V := ι (v 2)+(ι b)*(ι q-ι (v 1))
    let rank : DiffRing V := ((ι q)*(ι q)-1)*G+ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q)
    (ι Bp : DiffRing V)<ι Bn →
      ∃ n : V, 2≤n ∧ 2*ycoord n (2*(P-1)+1)=k ∧
        (ι q : DiffRing V)^4 ∣ 2*ι n-rank-1 := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let P : V := (X*Y)*Y
  let B : V := 2*(P-1)+1
  let k : V := v 8+v 9
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let G : DiffRing V := ι (v 2)+(ι b)*(ι q-ι (v 1))
  let rank : DiffRing V := ((ι q)*(ι q)-1)*G+ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q)
  change (ι Bp : DiffRing V)<ι Bn → ∃ n : V, 2≤n ∧ 2*ycoord n B=k ∧
    (ι q : DiffRing V)^4 ∣ 2*ι n-rank-1
  intro hn
  have hq : 0<q := by dsimp [q]; simp
  have hX : 0<X := mul_pos hq (hv 5)
  have hY : 0<Y := mul_pos (mul_pos hq (mul_pos hq hq)) (hv 6)
  have hP : 0<P := mul_pos (mul_pos hX hY) hY
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hD : discriminant (P-1)=P*(P+1) := by
    unfold discriminant
    rw [show P-1+2=(P-1+1)+1 by ring,hP1]
  have hb0 : 0<v 0*(p 0:V) := mul_pos (hv 0) hb
  obtain ⟨tau,_,_,htau⟩ := first_root p v hz hb0
  change tau*tau=1+P*(P+1)*k*k at htau
  rw [←hD] at htau
  obtain ⟨n,_,s,_,_,hnk,_,hks⟩ := solution_residues (P-1) tau k htau
  rw [hP1] at hks
  change 2*ycoord n B=k at hnk
  have hkgt : (2:V)<k := by
    have hg := graph_gap p v hb hv hz
    change 8*P+4≤k at hg
    have h4 : (4:V)≤8*P+4 := by exact le_add_self
    exact lt_of_lt_of_le (by norm_num : (2:V)<4) (le_trans h4 hg)
  have hn2 : 2≤n := by
    by_contra hn2
    have hnle : n≤1 := lt_two_iff_le_one.mp (lt_of_not_ge hn2)
    have hy := (y_strictMono B).monotone hnle
    have hyone : ycoord (1:V) B=1 := by simpa using (y_succ (0:V) B)
    have hm := mul_le_mul_of_nonneg_left hy (show (0:V)≤2 by simp)
    rw [hyone,hnk] at hm
    exact (not_le_of_gt hkgt) (by simpa using hm)
  have hPd : q^4∣P := ⟨q^3*v 5*(v 6*v 6),by dsimp [P,X,Y]; ring⟩
  obtain ⟨d,hd⟩ := hPd
  have hPembed : (ι P : DiffRing V)=(ι q)^4*ι d := by
    have hh := congrArg (fun x : V => (ι x : DiffRing V)) hd
    simpa only [map_mul,map_pow] using hh
  have hkembed : (ι k : DiffRing V)=2*ι n+4*ι P*ι s := by
    have hh := congrArg (fun x : V => (ι x : DiffRing V)) hks
    simpa only [map_add,map_mul,map_ofNat] using hh
  have htail : (ι q : DiffRing V)^4 ∣ ι k-2*ι n := by
    refine ⟨4*ι d*ι s,?_⟩
    rw [hkembed,hPembed]
    ring
  have hrank := graph_signed_rank_congruence p v hb hv hz hn
  change (ι q : DiffRing V)^4 ∣ ι k-rank-1 at hrank
  have hdiff := dvd_sub hrank htail
  refine ⟨n,hn2,hnk,?_⟩
  convert hdiff using 1
  ring

#print axioms Absorb88SignedEarlyIndex.graph_signed_early
end Absorb88SignedEarlyIndex
