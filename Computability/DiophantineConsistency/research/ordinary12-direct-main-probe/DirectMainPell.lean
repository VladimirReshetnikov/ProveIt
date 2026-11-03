import DirectMainNorm
import DiophantineConsistency.ArithmeticAdaptivePellIndices2011

/-! Conditional Pell classification without the old graph's signed pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainPell
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticSignedPairs DirectMainNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The two norm equations give positive Pell indices and coordinate bounds. -/
theorem indices_of_norms (Q k a c first main : V)
    (hQ : 0<Q) (hk : 0<k) (hc : 0<c)
    (hn : first*first=1+Q*(Q+1)*k*k)
    (hm : main*main=1+delta a*c*c) :
    ∃ n m : V, 0<n ∧ 0<m ∧ n≤k ∧ m≤c ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c := by
  obtain ⟨n,hnk,hnx,hny⟩ := ArithmeticPellFirstNorm.positive_parameter_solution Q first k hQ hn
  obtain ⟨m,hmc,hmx,hmy⟩ := ArithmeticPellClassification.solution_index a main c hm
  have hnp : 0<n := pos_iff_ne_zero.mpr (fun h => (ne_of_gt hk) (by simpa [h] using hny.symm))
  have hmp : 0<m := pos_iff_ne_zero.mpr (fun h => (ne_of_gt hc) (by simpa [h] using hmy.symm))
  exact ⟨n,m,hnp,hmp,hnk,hmc,hnx,hny,hmx,hmy⟩

/-- Direct-main orientation and both assumed norms produce positive Pell
indices without requiring equivalence to the old graph's signed main pair. -/
theorem direct_indices (U X Y k eta G R first : V)
    (hU : 0<U) (hX : 0<X) (hY : 8≤Y) (hk : 0<k) (heta : 0<eta)
    (hfirst : first*first=1+((X*Y)*Y)*(((X*Y)*Y)+1)*k*k)
    (hnorm :
      let a := X*Y+Y
      let c := eta+Y*k
      let H := 3+4*a
      let P := U*(X+a*c)+H*(U*G+R+1)
      let N := H*k
      magnitude (P,N)*magnitude (P,N)=U*U*(1+(H+a*a)*(c*c))) :
    let a := X*Y+Y
    let c := eta+Y*k
    let H := 3+4*a
    let P := U*(X+a*c)+H*(U*G+R+1)
    let N := H*k
    let Q := (X*Y)*Y
    ∃ main n m : V, 0<main ∧ P=N+U*main ∧ 0<n ∧ 0<m ∧ n≤k ∧ m≤c ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c := by
  let a := X*Y+Y
  let c := eta+Y*k
  let H := 3+4*a
  let Q := (X*Y)*Y
  have hypos : 0<Y := lt_of_lt_of_le (by simp : (0:V)<8) hY
  have hQ : 0<Q := mul_pos (mul_pos hX hypos) hypos
  have hc : 0<c := add_pos heta (mul_pos hypos hk)
  obtain ⟨main,hm,hbalance,hnormmain⟩ := direct_main_orientation U X Y k eta G R hU hY hk hnorm
  have hmn : main*main=1+delta a*c*c := by
    calc
      main*main=1+(H+a*a)*(c*c) := hnormmain
      _=1+delta a*c*c := by dsimp [H,delta]; ring
  obtain ⟨n,m,hn,hm',hnk,hmc,hnx,hny,hmx,hmy⟩ :=
    indices_of_norms Q k a c first main hQ hk hc hfirst hmn
  exact ⟨main,n,m,hm,hbalance,hn,hm',hnk,hmc,hnx,hny,hmx,hmy⟩

#print axioms DirectMainPell.indices_of_norms
#print axioms DirectMainPell.direct_indices
end DirectMainPell
