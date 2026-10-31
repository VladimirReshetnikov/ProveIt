import DiophantineConsistency.AdaptiveGap85Indices
import DiophantineConsistency.AdaptiveGap85FirstDivisibility
import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011

/-! Ordering of the actual 85 first and main Pell indices. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85IndexOrder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticPellRecurrence ArithmeticPellCongruences
open AdaptiveGap85Literal AdaptiveGap85Indices AdaptiveGap85FirstDivisibility
open ArithmeticAdaptiveIndexComparison2011 (base_mono two_le_of_positive_cube_quotient)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first index is strictly smaller than the main index; neither root is oriented. -/
theorem expressionAt_index_order85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let Q : V := (v 6*v 7)*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    ∃ first main n m : V, 0<n ∧ n<m ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c := by
  have hY : 2≤v 7 := two_le_of_positive_cube_quotient
    (scaled_parameters_positive p v hb hv).1 (expressionAt_Y_quotient85 p v hb hv hz)
  let E : V := v 6*v 7
  let Y : V := v 7
  let Q : V := E*Y
  let B : V := 2*(Q-1)+1
  let k : V := v 9+v 10
  let c : V := v 9+Y*k
  let a : V := E+Y
  have hE : 0<E := mul_pos (hv 6) (hv 7)
  have hk : 0<k := add_pos (hv 9) (hv 10)
  have hQ1 : Q-1+1=Q := tsub_add_cancel_of_le (pos_iff_one_le.mp (mul_pos hE (hv 7)))
  have hB : B+2=2*Q+1 := by
    dsimp [B]
    calc
      2*(Q-1)+1+2=2*(Q-1+1)+1 := by ring
      _=2*Q+1 := by rw [hQ1]
  have hab : a≤B := by
    have hEsub : E-1+1=E := tsub_add_cancel_of_le (pos_iff_one_le.mp hE)
    have hYsub : Y-2+2=Y := tsub_add_cancel_of_le hY
    have heq : a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=B+2 := by
      rw [hB]
      calc
        a+2+(E-1)*(2*(Y-2)+3)+(Y-2)=
          (E-1+1)+(Y-2+2)+2+(E-1)*(2*(Y-2)+3)+(Y-2) := by rw [hEsub,hYsub]
        _=2*((E-1+1)*(Y-2+2))+1 := by ring
        _=2*Q+1 := by rw [hEsub,hYsub]
    have heq' : a+2≤B+2 := by rw [←heq]; simp
    exact (add_le_add_iff_right (2:V)).mp heq'
  obtain ⟨first,main,n,m,hf,hm,hnp,hmp,hnk,hmc,hroot,hmain,hnx,hny,hmx,hmy⟩ := expressionAt_indices85 p v hb hv hz
  change 2*ycoord n B=k at hny
  change ycoord m a=c at hmy
  have hkc : k<c := calc
    k≤k*Y := le_mul_of_one_le_right (by simp) (le_trans (by simp : (1:V)≤2) hY)
    _<k*Y+v 9 := lt_add_of_pos_right _ (hv 9)
    _=c := by dsimp [c]; ring
  have hnm : n<m := by
    by_contra hn
    have hm : m≤n := le_of_not_gt hn
    have hc : c≤k := calc
      c=ycoord m a := hmy.symm
      _≤ycoord n a := (y_strictMono a).monotone hm
      _≤ycoord n B := (base_mono a B hab n).2
      _≤2*ycoord n B := le_mul_of_one_le_left (by simp) (by simp)
      _=k := hny
    exact (not_le_of_gt hkc) hc
  exact ⟨first,main,n,m,hnp,hnm,hnx,hny,hmx,hmy⟩
end DiophantineConsistency.AdaptiveGap85IndexOrder
