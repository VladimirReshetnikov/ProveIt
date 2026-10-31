import DiophantineConsistency.AdaptiveGap85RankCongruence
import DiophantineConsistency.AdaptiveGap85Indices

/-! First Pell index congruence to the actual signed 85 rank. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FirstRankResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveFirstDivisibility2011
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticPellRecurrence ArithmeticPellCongruences
open AdaptiveGap85Literal AdaptiveGap85FirstDivisibility AdaptiveGap85Indices AdaptiveGap85RankCongruence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An actual zero yields a positive first Pell index whose double is congruent to
one plus the signed rank, without assuming the sign or a rank window. -/
theorem expressionAt_first_rank_residue85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let q2 : V := q*q
    let Q : V := (v 6*v 7)*v 7
    let k : V := v 9+v 10
    let neg : V := q*v 1+v 2
    let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
    let rn : V := q2+neg*q2
    ∃ first n : V, 0<first ∧ 0<n ∧ n≤k ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      (rp+1)%(q^4)=(rn+2*n)%(q^4) := by
  let q : V := 1+v 0*(p 0:V)
  let q2 : V := q*q
  let Q : V := (v 6*v 7)*v 7
  let B : V := 2*(Q-1)+1
  let k : V := v 9+v 10
  let neg : V := q*v 1+v 2
  let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
  let rn : V := q2+neg*q2
  have hq : 0<q := by dsimp [q]; simp
  have hm : 0<q^4 := pow_pos hq _
  have hQ : 0<Q := mul_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp hQ)
  have hB : B+1=2*Q := by
    dsimp [B]
    calc
      2*(Q-1)+1+1=2*(Q-1+1) := by ring
      _=2*Q := by rw [hQ1]
  obtain ⟨s,_,hs⟩ := expressionAt_Y_quotient85 p v hb hv hz
  have hs' : v 7=q^3*s := by dsimp [q]; rw [hs]; ring
  have hdiv : q^4∣B+1 := by
    rw [hB]
    refine ⟨2*v 6*(q*q)*s*s,?_⟩
    dsimp [Q]; rw [hs']; ring
  obtain ⟨first,main,n,m,hfirst,_,hn,_,hnk,_,_,_,hnx,hny,_,_⟩ := expressionAt_indices85 p v hb hv hz
  have hrc := expressionAt_rank_congruence85 p v hb hv hz
  change q^4∣magnitude (rp+1,rn+k) at hrc
  have hres : (rp+1)%(q^4)=(rn+k)%(q^4) := magnitude_mod (rp+1,rn+k) (q^4) hm hrc
  obtain ⟨r,t,_,hy⟩ := residue_quotients n B (q^4) hdiv
  change 2*ycoord n B=k at hny
  have hk : k=2*n+q^4*(2*t) := by rw [←hny,hy]; ring
  rw [hk,show rn+(2*n+q^4*(2*t))=(rn+2*n)+q^4*(2*t) by ring,
    mod_add_mul' _ _ hm] at hres
  exact ⟨first,n,hfirst,hn,hnk,hnx,hny,hres⟩
end DiophantineConsistency.AdaptiveGap85FirstRankResidue
