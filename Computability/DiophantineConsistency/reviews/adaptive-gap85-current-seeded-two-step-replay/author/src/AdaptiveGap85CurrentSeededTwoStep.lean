import DiophantineConsistency.AdaptiveGap85SeededTwoStep
import DiophantineConsistency.AdaptiveGap85CurrentIndices
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85CurrentSeededTwoStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveGap85Literal ArithmeticPellRecurrence ArithmeticPellCongruences
open ArithmeticAdaptiveScaledNorms2011 AdaptiveGap85CurrentNoFourth AdaptiveGap85CurrentIndices
open AdaptiveGap85SeededTwoStep AdaptiveGap85InverseEntry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The fixed-port R≥5 premise follows from the actual full zero and the
Pell-coordinate equation. Scaling and the two seed equations remain explicit. -/
theorem current_seeded_gap_zero_two_step (z : Fin 13 → V) (R u iSeed : V)
    (hz : ∀i,0<z i)
    (hzero : InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) z)
    (hgapz : z 1+z 2<1+z 0*(currentPorts 0:V))
    (hc : z 9+z 7*(z 9+z 10)=ycoord R (z 6*z 7+z 7))
    (hscale : z 4=delta (z 6*z 7+z 7)*iSeed)
    (hux : let a := z 6*z 7+z 7; let c := z 9+z 7*(z 9+z 10)
      let I := delta a*iSeed*c*c; xcoord R (I-2)=I*u)
    (he : let c := z 9+z 7*(z 9+z 10)
      z 3*z 3*c*z 5=u+c+z 3*z 3*R) :
    ∃ a m : Fin 13 → V, (∀i,0<a i) ∧ (∀i,0<m i) ∧
      InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) a ∧
      InternalZero (expressionAt85 (fun j => (currentPorts j:ℤ))) m ∧
      ¬(a 1+a 2<1+a 0*(currentPorts 0:V)) ∧ ¬(m 1+m 2<1+m 0*(currentPorts 0:V)) ∧
      z 1+z 2<1+z 0*(currentPorts 0:V) ∧
      PositiveBiStep currentPorts a m ∧ PositiveBiStep currentPorts m z ∧
      ¬∃ x : Fin 13 → V, PositiveBiStep currentPorts a x ∧ x 1+x 2<1+x 0*(currentPorts 0:V) := by
  let a : V := z 6*z 7+z 7
  let c : V := z 9+z 7*(z 9+z 10)
  have hb : 0<(currentPorts 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<4) current_first_port_four
  have hb2 : 2≤z 0*(currentPorts 0:V) := by
    have hJ : 1≤z 0 := pos_iff_one_le.mp (hz 0)
    have hmul : (currentPorts 0:V)≤z 0*(currentPorts 0:V) := by
      simpa only [one_mul] using Arithmetic.mul_le_mul_right (a:=(currentPorts 0:V)) hJ
    exact le_trans (by norm_num : (2:V)≤4) (le_trans current_first_port_four hmul)
  obtain ⟨first,main,n,m,hn,hm,hnm,hnx,hny,hmx,hmy⟩ := current_zero_index_bounds z hz hzero
  change c=ycoord R a at hc
  change ycoord m a=c at hmy
  have hRm : R=m := (y_strictMono a).injective (hc.symm.trans hmy.symm)
  have hR : 5≤R := by rw [hRm]; exact hm
  exact seeded_gap_zero_two_step currentPorts z R u iSeed hb hb2 hz hzero hgapz hR hc hscale hux he
end DiophantineConsistency.AdaptiveGap85CurrentSeededTwoStep
