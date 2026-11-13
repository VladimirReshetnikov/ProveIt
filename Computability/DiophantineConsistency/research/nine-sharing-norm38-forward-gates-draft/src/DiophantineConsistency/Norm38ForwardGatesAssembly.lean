import DiophantineConsistency.Norm38ForwardGates00
import DiophantineConsistency.Norm38ForwardGates01
import DiophantineConsistency.Norm38ForwardGates02
import DiophantineConsistency.Norm38ForwardGates03
import DiophantineConsistency.Norm38ForwardGates04
import DiophantineConsistency.Norm38ForwardGates05
import DiophantineConsistency.Norm38ForwardGates06
import DiophantineConsistency.Norm38ForwardGates07
import DiophantineConsistency.Norm38ForwardGates08
import DiophantineConsistency.Norm38ForwardGates09
import DiophantineConsistency.Norm38ForwardGates10
import DiophantineConsistency.Norm38ForwardGates11
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38ForwardGates
open SharingGateModel
variable {S R : Type*} [CommSemiring S] [CommRing R]

/-- Proposed finite assembly, with no source norm assumptions. -/
theorem forward_gatesHold (embed : S →+* R) (ports : Fin 4 → S) (u : Fin 14 → S) :
    NormAssignment38.gatesHold embed ports (SharingForward38.witnessCoordinates ports u) := by
  unfold NormAssignment38.gatesHold
  simp only [NormAssignment38.gates, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
    false_implies, forall_const, and_true]
  exact ⟨forwardGate21 embed ports u,
    forwardGate22 embed ports u,
    forwardGate23 embed ports u,
    forwardGate24 embed ports u,
    forwardGate25 embed ports u,
    forwardGate26 embed ports u,
    forwardGate27 embed ports u,
    forwardGate28 embed ports u,
    forwardGate29 embed ports u,
    forwardGate30 embed ports u,
    forwardGate31 embed ports u,
    forwardGate32 embed ports u,
    forwardGate33 embed ports u,
    forwardGate34 embed ports u,
    forwardGate35 embed ports u,
    forwardGate36 embed ports u,
    forwardGate37 embed ports u,
    forwardGate38 embed ports u,
    forwardGate39 embed ports u,
    forwardGate40 embed ports u,
    forwardGate41 embed ports u,
    forwardGate42 embed ports u,
    forwardGate43 embed ports u,
    forwardGate44 embed ports u,
    forwardGate45 embed ports u,
    forwardGate46 embed ports u,
    forwardGate47 embed ports u,
    forwardGate48 embed ports u,
    forwardGate49 embed ports u,
    forwardGate50 embed ports u,
    forwardGate51 embed ports u,
    forwardGate52 embed ports u,
    forwardGate53 embed ports u,
    forwardGate54 embed ports u,
    forwardGate55 embed ports u,
    forwardGate56 embed ports u,
    forwardGate57 embed ports u,
    forwardGate58 embed ports u,
    forwardGate59 embed ports u,
    forwardGate60 embed ports u,
    forwardGate61 embed ports u,
    forwardGate62 embed ports u,
    forwardGate63 embed ports u,
    forwardGate64 embed ports u,
    forwardGate65 embed ports u,
    forwardGate66 embed ports u,
    forwardGate67 embed ports u,
    forwardGate68 embed ports u,
    forwardGate69 embed ports u,
    forwardGate70 embed ports u,
    forwardGate71 embed ports u,
    forwardGate72 embed ports u,
    forwardGate73 embed ports u,
    forwardGate74 embed ports u,
    forwardGate75 embed ports u,
    forwardGate76 embed ports u,
    forwardGate77 embed ports u,
    forwardGate78 embed ports u,
    forwardGate79 embed ports u,
    forwardGate80 embed ports u, by simp⟩

end DiophantineConsistency.Norm38ForwardGates
