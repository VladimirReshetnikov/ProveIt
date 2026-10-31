import DiophantineConsistency.AdaptiveGap85FirstRankResidue
import DiophantineConsistency.AdaptiveGap85RankOrientation

/-! Conditional orientation and exact first-index relation for an actual 85 zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85OrientedRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellCongruences ArithmeticPellHalfIndex
open AdaptiveGap85Literal AdaptiveGap85FirstRankResidue AdaptiveGap85RankOrientation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive actual zero with a sufficiently small signed rank has positive
rank orientation and exact rank-plus-one equal to twice the first index. -/
theorem expressionAt_oriented_rank85 (p : Fin 4 → ℕ) (v : Fin 13 → V) (n : V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v)
    (hn : 0<n)
    (hny : 2*ycoord n (2*((v 6*v 7)*v 7-1)+1)=v 9+v 10)
    (hsmall : let q : V := 1+v 0*(p 0:V)
      let q2 : V := q*q
      let neg : V := q*v 1+v 2
      let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
      let rn : V := q2+neg*q2
      absdiff rp rn+2*n<q^4) :
    let q : V := 1+v 0*(p 0:V)
    let q2 : V := q*q
    let neg : V := q*v 1+v 2
    let rp : V := q2*q2+neg+v 0*((p 2:V)+(p 3:V)*q)
    let rn : V := q2+neg*q2
    rn<rp ∧ absdiff rp rn+1=2*n := by
  obtain ⟨first,j,_,_,_,_,hjy,hres⟩ := expressionAt_first_rank_residue85 p v hb hv hz
  have he : ycoord j (2*((v 6*v 7)*v 7-1)+1)=ycoord n (2*((v 6*v 7)*v 7-1)+1) := by
    apply mul_left_cancel₀ (by norm_num : (2:V)≠0)
    exact hjy.trans hny.symm
  have hj : j=n := index_unique _ _ _ he
  subst j
  have hq : 0<(1+v 0*(p 0:V))^4 := pow_pos (by simp) _
  exact positive_rank_of_small_residue _ _ _ n hq hn hsmall hres
end DiophantineConsistency.AdaptiveGap85OrientedRank
