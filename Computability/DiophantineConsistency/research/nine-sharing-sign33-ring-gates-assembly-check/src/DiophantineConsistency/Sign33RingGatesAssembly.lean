import DiophantineConsistency.Sign33RingGates00
import DiophantineConsistency.Sign33RingGates01
import DiophantineConsistency.Sign33RingGates02
import DiophantineConsistency.Sign33RingGates03
import DiophantineConsistency.Sign33RingGates04
import DiophantineConsistency.Sign33RingGates05
import DiophantineConsistency.Sign33RingGates06
import DiophantineConsistency.Sign33RingGates07
import DiophantineConsistency.Sign33RingGates08
import DiophantineConsistency.Sign33RingGates09
import DiophantineConsistency.Sign33RingGates10
import DiophantineConsistency.Sign33RingGates11

/-! Assemble all 60 fixed-valuation ring gate equations. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33RingGatesAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing SharingGateModel
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem all_ring_gates (ports : Fin 4 → V) (v : Fin 34 → V)
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    let env := fun i => pairValue ι (NormAssignment38.assignment ports (Sign33Lift38.lift v) i)
    ∀ g ∈ NormAssignment38.gates,
      env g.target = ringCompute g.op (env g.left) (env g.right) := by
  simp only [NormAssignment38.gates, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    false_implies, forall_const, and_true]
  exact ⟨Sign33RingGates00.gate21 ports v,
    Sign33RingGates00.gate22 ports v,
    Sign33RingGates00.gate23 ports v hc,
    Sign33RingGates01.gate24 ports v hc,
    Sign33RingGates01.gate25 ports v hc,
    Sign33RingGates01.gate26 ports v hc,
    Sign33RingGates02.gate27 ports v hc,
    Sign33RingGates02.gate28 ports v,
    Sign33RingGates02.gate29 ports v hc,
    Sign33RingGates03.gate30 ports v hc,
    Sign33RingGates03.gate31 ports v,
    Sign33RingGates03.gate32 ports v,
    Sign33RingGates03.gate33 ports v,
    Sign33RingGates03.gate34 ports v,
    Sign33RingGates03.gate35 ports v,
    Sign33RingGates04.gate36 ports v hc,
    Sign33RingGates04.gate37 ports v,
    Sign33RingGates04.gate38 ports v,
    Sign33RingGates04.gate39 ports v,
    Sign33RingGates04.gate40 ports v hc,
    Sign33RingGates04.gate41 ports v hc,
    Sign33RingGates05.gate42 ports v hc,
    Sign33RingGates05.gate43 ports v,
    Sign33RingGates05.gate44 ports v,
    Sign33RingGates05.gate45 ports v,
    Sign33RingGates05.gate46 ports v,
    Sign33RingGates05.gate47 ports v,
    Sign33RingGates06.gate48 ports v hc,
    Sign33RingGates06.gate49 ports v,
    Sign33RingGates06.gate50 ports v,
    Sign33RingGates06.gate51 ports v,
    Sign33RingGates06.gate52 ports v,
    Sign33RingGates06.gate53 ports v,
    Sign33RingGates07.gate54 ports v,
    Sign33RingGates07.gate55 ports v,
    Sign33RingGates07.gate56 ports v,
    Sign33RingGates07.gate57 ports v hc,
    Sign33RingGates07.gate58 ports v,
    Sign33RingGates07.gate59 ports v,
    Sign33RingGates08.gate60 ports v,
    Sign33RingGates08.gate61 ports v,
    Sign33RingGates08.gate62 ports v,
    Sign33RingGates08.gate63 ports v,
    Sign33RingGates08.gate64 ports v,
    Sign33RingGates08.gate65 ports v,
    Sign33RingGates09.gate66 ports v,
    Sign33RingGates09.gate67 ports v hc,
    Sign33RingGates09.gate68 ports v,
    Sign33RingGates09.gate69 ports v hc,
    Sign33RingGates09.gate70 ports v,
    Sign33RingGates09.gate71 ports v hc,
    Sign33RingGates10.gate72 ports v hc,
    Sign33RingGates10.gate73 ports v hc,
    Sign33RingGates10.gate74 ports v,
    Sign33RingGates10.gate75 ports v,
    Sign33RingGates10.gate76 ports v hc,
    Sign33RingGates10.gate77 ports v,
    Sign33RingGates11.gate78 ports v,
    Sign33RingGates11.gate79 ports v,
    Sign33RingGates11.gate80 ports v,
    by simp⟩
end DiophantineConsistency.Sign33RingGatesAssembly
#print axioms DiophantineConsistency.Sign33RingGatesAssembly.all_ring_gates
