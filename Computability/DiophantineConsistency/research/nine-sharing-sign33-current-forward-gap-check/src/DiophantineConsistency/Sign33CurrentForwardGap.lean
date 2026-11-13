import DiophantineConsistency.Sign33ForwardGap
import DiophantineConsistency.Sign33CurrentCoreCuts

/-! Current source supplies representatives and the first signed cut. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33CurrentForwardGap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_has_representatives_and_gap (ports : Fin 4 → V) (u : Fin 14 → V)
    (hp : ∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j))
    (hz : ObjectCurrentEquation2011.InternalZero ObjectCurrentEquation2011.naturalExpression u) :
    let d := Carrier65.core (ModelThirteenCarrier.ringPorts (V := V)) (fun j => ι (u j+1))
    ∃ gap tau inner value negative : V,
      (let v := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
       ι (v 26) = (Sign33ResidualBatch04.t ports v*(Sign33ResidualBatch04.t ports v+1)+(ι (v 3)+1))-
          Sign33ResidualBatch04.t ports v*(ι (v 2)+1)) ∧
      ι tau = d.tau ∧ ι inner = d.c*ι (u 6+1)-d.rank ∧
      ι value = d.V ∧ ι negative = d.y*d.y-d.V*d.V := by
  obtain ⟨gap,tau,inner,value,negative,hgap,htau,hinner,hvalue,hnegative⟩ :=
    Sign33CurrentCoreCuts.five_core_representatives_of_current_zero u hz
  have hports : (fun j => ι (ports j)) = ModelThirteenCarrier.ringPorts (V := V) := by
    funext j
    exact (hp j).symm
  have hgap' : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι gap = (d.q-1)*(d.q-ι (u 1+1))+ι (u 2+1) := by
    rw [hports]
    exact hgap
  exact ⟨gap,tau,inner,value,negative,
    Sign33ForwardGap.gap_of_core ports u gap tau inner value negative hgap',
    htau,hinner,hvalue,hnegative⟩
end DiophantineConsistency.Sign33CurrentForwardGap
#print axioms DiophantineConsistency.Sign33CurrentForwardGap.source_has_representatives_and_gap
