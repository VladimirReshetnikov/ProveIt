import DiophantineConsistency.Sign33ForwardGroup00
import DiophantineConsistency.Sign33ForwardGroup01
import DiophantineConsistency.Sign33ForwardGroup02
import DiophantineConsistency.Sign33ForwardGroup03Positive
import DiophantineConsistency.Sign33ForwardLatePositive
import DiophantineConsistency.Sign33ForwardGap
import DiophantineConsistency.Sign33ForwardTau
import DiophantineConsistency.Sign33ForwardInner
import DiophantineConsistency.Sign33ForwardValueNegative
import DiophantineConsistency.Sign33ForwardNormQRetry
import DiophantineConsistency.Sign33ForwardNormW
import DiophantineConsistency.Sign33ForwardNormP
import DiophantineConsistency.Sign33ForwardNormStrong
import DiophantineConsistency.Sign33ForwardNormU

/-! Source-only candidate assembly: same-valuation constructor AllCuts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardAllCuts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem all_cuts_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hgap : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1));
      ι gap = (d.q-1)*(d.q-ι (u 1+1))+ι (u 2+1))
    (htau : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1)); ι tau = d.tau)
    (hinner : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1)); ι inner = d.c*ι (u 6+1)-d.rank)
    (hvalue : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1)); ι value = d.V)
    (hnegative : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1)); ι negative = d.y*d.y-d.V*d.V)
    (hnorms : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1));
      d.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1) :
    Sign33ResidualAssembly.AllCuts ports
      (Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)) := by
  have h00 := Sign33ForwardGroup00.constructor_cuts ports u gap tau inner value negative
  have h01 := Sign33ForwardGroup01.constructor_cuts ports u gap tau inner value negative
  have h02 := Sign33ForwardGroup02.constructor_cuts ports u gap tau inner value negative
  have h03 := Sign33ForwardGroup03Positive.constructor_cuts ports u gap tau inner value negative
  have hlate := Sign33ForwardLatePositive.constructor_cuts ports u gap tau inner value negative
  have hgapcut := Sign33ForwardGap.gap_of_core ports u gap tau inner value negative hgap
  have htaucut := Sign33ForwardTau.tau_of_core ports u gap tau inner value negative hgap htau
  have hinnercut := Sign33ForwardInner.inner_of_core ports u gap tau inner value negative hgap hinner
  have hvaluecut := Sign33ForwardValueNegative.value_of_core ports u gap tau inner value negative hinner hvalue
  have hnegativecut := Sign33ForwardValueNegative.negative_of_core ports u gap tau inner value negative hvalue hnegative
  rcases hnorms with ⟨hp,hq,hu,hs,hw⟩
  have hpcut := Sign33ForwardNormP.norm_p_of_core ports u gap tau inner value negative htau hp
  have hqcut := Sign33ForwardNormQRetry.norm_q_of_core ports u gap tau inner value negative hq
  have hucut := Sign33ForwardNormU.norm_u_of_core ports u gap tau inner value negative hnegative hu
  have hscut := Sign33ForwardNormStrong.norm_strong_of_core ports u gap tau inner value negative hs
  have hwcut := Sign33ForwardNormW.norm_w_of_core ports u gap tau inner value negative hw
  exact ⟨h00, h01, h02, ⟨h03.1, h03.2, hqcut⟩,
    ⟨hgapcut, htaucut, hpcut⟩, ⟨hwcut, hlate.1, hinnercut⟩,
    ⟨hvaluecut, hlate.2.1, hlate.2.2⟩, ⟨hnegativecut, hucut, hscut⟩⟩
end DiophantineConsistency.Sign33ForwardAllCuts
#print axioms DiophantineConsistency.Sign33ForwardAllCuts.all_cuts_of_core
