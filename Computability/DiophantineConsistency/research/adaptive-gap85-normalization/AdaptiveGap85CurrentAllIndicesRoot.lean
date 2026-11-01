import DiophantineConsistency.AdaptiveGap85ActualAllIndicesRoot
import DiophantineConsistency.AdaptiveGap85CurrentIndices
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85CurrentAllIndicesRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence ArithmeticPellCongruences
open ArithmeticAdaptiveScaledNorms2011 AdaptiveGap85Literal AdaptiveGap85CurrentNoFourth
open AdaptiveGap85CurrentIndices AdaptiveGap85ActualAllIndicesRoot
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The fixed-port index bounds and arbitrary-index root congruences refer to
the same Pell witnesses. They do not rule out a zero. -/
theorem current_zero_indices_root_congruences (v : Fin 13 → V)
    (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) v) :
    let Q : V := (v 6*v 7)*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := v 6*v 7+v 7
    let H : V := 4*(v 7*(v 6+1))+3
    ∃ first main n m : V, 3≤n ∧ 5≤m ∧ n<m ∧
      xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧
      xcoord m a=main ∧ ycoord m a=c ∧
      ((27*v 6)%H=(27*Exp.exp m)%H ∨ (27*(1+Exp.exp m*v 6))%H=0) := by
  let a : V := v 6*v 7+v 7
  let c : V := v 9+v 7*(v 9+v 10)
  have hb : 0<(currentPorts 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<4) current_first_port_four
  obtain ⟨m,hmp,hmy,hcong⟩ := actual_zero_root_congruences currentPorts v hb hv hz
  obtain ⟨first,main,n,m',hn,hm,hnm,hnx,hny,hmx,hmy'⟩ := current_zero_index_bounds v hv hz
  change ycoord m a=c at hmy
  change ycoord m' a=c at hmy'
  have he : m=m' := (y_strictMono a).injective (hmy.trans hmy'.symm)
  subst m'
  exact ⟨first,main,n,m,hn,hm,hnm,hnx,hny,hmx,hmy',hcong⟩
end DiophantineConsistency.AdaptiveGap85CurrentAllIndicesRoot
