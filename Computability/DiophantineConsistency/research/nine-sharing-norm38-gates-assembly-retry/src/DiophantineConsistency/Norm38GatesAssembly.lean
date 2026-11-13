import DiophantineConsistency.Norm38Gates00
import DiophantineConsistency.Norm38Gates01
import DiophantineConsistency.Norm38Gates02
import DiophantineConsistency.Norm38Gates03
import DiophantineConsistency.Norm38Gates04
import DiophantineConsistency.Norm38Gates05
import DiophantineConsistency.Norm38Gates06
import DiophantineConsistency.Norm38Gates07
import DiophantineConsistency.Norm38Gates08
import DiophantineConsistency.Norm38Gates09
import DiophantineConsistency.Norm38Gates10
import DiophantineConsistency.Norm38Gates11
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38GateExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel Norm38SlotExtraction
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed final 60-gate assembly; no source graph equivalence is claimed. -/
theorem seed_zero_gatesHold (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    NormAssignment38.gatesHold ι ports w := by
  unfold NormAssignment38.gatesHold
  simp only [NormAssignment38.gates, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    false_implies, forall_const, and_true]
  exact ⟨gate21 p ports w hp hz,
    gate22 p ports w hp hz,
    gate23 p ports w hp hz,
    gate24 p ports w hp hz,
    gate25 p ports w hp hz,
    gate26 p ports w hp hz,
    gate27 p ports w hp hz,
    gate28 p ports w hp hz,
    gate29 p ports w hp hz,
    gate30 p ports w hp hz,
    gate31 p ports w hp hz,
    gate32 p ports w hp hz,
    gate33 p ports w hp hz,
    gate34 p ports w hp hz,
    gate35 p ports w hp hz,
    gate36 p ports w hp hz,
    gate37 p ports w hp hz,
    gate38 p ports w hp hz,
    gate39 p ports w hp hz,
    gate40 p ports w hp hz,
    gate41 p ports w hp hz,
    gate42 p ports w hp hz,
    gate43 p ports w hp hz,
    gate44 p ports w hp hz,
    gate45 p ports w hp hz,
    gate46 p ports w hp hz,
    gate47 p ports w hp hz,
    gate48 p ports w hp hz,
    gate49 p ports w hp hz,
    gate50 p ports w hp hz,
    gate51 p ports w hp hz,
    gate52 p ports w hp hz,
    gate53 p ports w hp hz,
    gate54 p ports w hp hz,
    gate55 p ports w hp hz,
    gate56 p ports w hp hz,
    gate57 p ports w hp hz,
    gate58 p ports w hp hz,
    gate59 p ports w hp hz,
    gate60 p ports w hp hz,
    gate61 p ports w hp hz,
    gate62 p ports w hp hz,
    gate63 p ports w hp hz,
    gate64 p ports w hp hz,
    gate65 p ports w hp hz,
    gate66 p ports w hp hz,
    gate67 p ports w hp hz,
    gate68 p ports w hp hz,
    gate69 p ports w hp hz,
    gate70 p ports w hp hz,
    gate71 p ports w hp hz,
    gate72 p ports w hp hz,
    gate73 p ports w hp hz,
    gate74 p ports w hp hz,
    gate75 p ports w hp hz,
    gate76 p ports w hp hz,
    gate77 p ports w hp hz,
    gate78 p ports w hp hz,
    gate79 p ports w hp hz,
    gate80 p ports w hp hz, by simp⟩

end DiophantineConsistency.Norm38GateExtraction
