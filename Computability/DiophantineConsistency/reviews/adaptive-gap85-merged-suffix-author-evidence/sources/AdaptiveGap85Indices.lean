import DiophantineConsistency.AdaptiveGap85Quotients
import DiophantineConsistency.ArithmeticPellFirstNorm

/-! Classification of the first and main norms of the actual 85 zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Indices
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticPellRecurrence
open AdaptiveGap85Literal AdaptiveGap85Quotients
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Both indices exist without orienting either signed root or assuming any relation between indices. -/
theorem expressionAt_indices85 (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let M : V := (q*(q*q))*(v 0*(p 0:V))
    let U : V := v 7*(q*q)
    let Q : V := (v 6*v 7)*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    ∃ first main n m : V, 0<first ∧ 0<main ∧ 0<n ∧ 0<m ∧ n≤k ∧ m≤c ∧
      magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).1) v)=M*first ∧
      magnitude (pairEval (rootTerm (AdaptiveGap85Factors.factors (fun j => (p j:ℤ))).2.1) v)=U*main ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c := by
  let Q : V := (v 6*v 7)*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  have hQ : 0<Q := mul_pos (mul_pos (hv 6) (hv 7)) (hv 7)
  have hk : 0<k := add_pos (hv 9) (hv 10)
  have hc : 0<c := add_pos (hv 9) (mul_pos (hv 7) hk)
  obtain ⟨first,main,hf,hm,hroot,hnorm,hmain,hmnorm⟩ := expressionAt_quotients85 p v hb hv hz
  have hn : first*first=1+Q*(Q+1)*k*k := by
    calc
      first*first=1+((v 6*v 7)*(v 7*k))*(((v 6*v 7)*(v 7*k))+k) := hnorm
      _=1+Q*(Q+1)*k*k := by dsimp [Q]; ring
  have hmn : main*main=1+delta a*c*c := by
    calc
      main*main=1+((3+4*a)+a*a)*(c*c) := hmnorm
      _=1+delta a*c*c := by unfold delta; ring
  obtain ⟨n,hnk,hnx,hny⟩ := ArithmeticPellFirstNorm.positive_parameter_solution Q first k hQ hn
  obtain ⟨m,hmc,hmx,hmy⟩ := ArithmeticPellClassification.solution_index a main c hmn
  have hnp : 0<n := pos_iff_ne_zero.mpr (fun h => (ne_of_gt hk) (by simpa [h] using hny.symm))
  have hmp : 0<m := pos_iff_ne_zero.mpr (fun h => (ne_of_gt hc) (by simpa [h] using hmy.symm))
  exact ⟨first,main,n,m,hf,hm,hnp,hmp,hnk,hmc,hroot,hmain,hnx,hny,hmx,hmy⟩
end DiophantineConsistency.AdaptiveGap85Indices
