import DiophantineConsistency.AdaptiveGap85CurrentNoFourth
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85CurrentIndexFive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticAdaptiveScaledNorms2011
open AdaptiveGap85Literal AdaptiveGap85IndexLowerBound AdaptiveGap85CurrentNoFourth
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive zero at the literal current ports has main Pell index at
least five. This is a necessary restriction, not a no-zero proof. -/
theorem current_zero_main_index_at_least_five (v : Fin 13 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) v) :
    let Q : V := (v 6*v 7)*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    ∃ first main n m : V, 2≤n ∧ 5≤m ∧ n<m ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c := by
  let a : V := v 6*v 7+v 7
  let c : V := v 9+v 7*(v 9+v 10)
  have hb : 0<(currentPorts 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<4) current_first_port_four
  obtain ⟨first,main,n,m,hn2,hm4,hnm,hnx,hny,hmx,hmy⟩ :=
    actual_zero_index_lower_bounds currentPorts v hb hv hz
  change ycoord m a=c at hmy
  have hmne : m≠4 := by
    intro he
    have hh : c=ycoord 4 a := by rw [←hmy,he]
    exact current_zero_not_fourth_main v hv hz hh
  have hm5 : 5≤m := by
    have hh := lt_iff_succ_le.mp (lt_of_le_of_ne hm4 (Ne.symm hmne))
    simpa only [show (4:V)+1=5 by ring] using hh
  exact ⟨first,main,n,m,hn2,hm5,hnm,hnx,hny,hmx,hmy⟩
end DiophantineConsistency.AdaptiveGap85CurrentIndexFive
