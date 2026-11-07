import DiophantineConsistency.Sign33ForwardNormU38
import DiophantineConsistency.Sign33Node78Factor
import DiophantineConsistency.Sign33NegativeNode76
import DiophantineConsistency.Sign33AbstractProjection32
import DiophantineConsistency.Norm38ForwardPrefix

/-! U transport using the checked node78 factor and negative representative. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardNormU
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm_u_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hn : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      ι negative = d.y*d.y-d.V*d.V)
    (hu : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      d.U = 1) :
    let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    (ι (v 13)+1)*(ι (v 13)+1)-ι (v 32)*ι (v 33) = 1 := by
  let w := SharingForward38.witnessCoordinates ports u
  let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
  have ht := Sign33ForwardNormU38.u_terminal ports u hu
  have hf := Sign33Node78Factor.node78 ι ports w
  have hs := Sign33NegativeNode76.negative_of_core ports u negative hn
  change pairValue ι (NormAssignment38.assignment ports w 78) = 1 at ht
  change ι negative + pairValue ι (NormAssignment38.assignment ports w 76) = 0 at hs
  have hs' : pairValue ι (NormAssignment38.assignment ports w 76) = - ι negative := by
    calc
      pairValue ι (NormAssignment38.assignment ports w 76) =
          (ι negative + pairValue ι (NormAssignment38.assignment ports w 76))-ι negative := by ring
      _ = - ι negative := by rw [hs]; ring
  rw [hf, hs'] at ht
  have hy : w 12 = u 12 := by
    simpa [w] using Norm38Forward.forward_prefix ports u (12 : Fin 14)
  rw [hy] at ht
  have hv13 : v 13 = u 12 := by
    have hindex : (12 : Fin 33).succ = (13 : Fin 34) := by decide
    dsimp only [v]
    rw [←hindex, Fin.cons_succ]
    exact SharingForward33.witness_inputs ports u gap tau inner value negative (12 : Fin 14)
  have hv32 : v 32 = w 35 := Sign33AbstractProjection32.project ports u gap tau inner value negative
  have hv33 : v 33 = negative := by simp [v, SharingForward33.witnessCoordinates]
  change (ι (v 13)+1)*(ι (v 13)+1)-ι (v 32)*ι (v 33) = 1
  rw [hv13, hv32, hv33]
  simp only [map_add, map_one] at ht
  convert ht using 1 <;> ring
end DiophantineConsistency.Sign33ForwardNormU
#print axioms DiophantineConsistency.Sign33ForwardNormU.norm_u_of_core
