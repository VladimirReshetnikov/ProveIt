import DiophantineConsistency.CompactedJonesSyntax
import DiophantineConsistency.ComputationRepresentation
import DiophantineConsistency.ScalarPRRepresentation
import DiophantineConsistency.ScalarPROptimizer
import DiophantineConsistency.DirectScalarEnumeratorCore

/-! # The nine-variable consistency equation as Matrix-free syntax

`ExplicitZFC.expression`, built without importing Mathlib's matrices (whose
`Matrix.map` collides with Foundation's) or the ZFC calibration modules.
The representation keeps the program's own predicate `∃ t, haltingTest t = 1`
instead of transporting it to ZFC refutability with `Rep.ofIff`; transport
changes no syntax, and `ExplicitZFC.expression_eq_syntax` proves the two
expressions equal. Model-internal (Foundation) modules can therefore name the
exact equation through this module. -/

namespace DiophantineConsistency.ExplicitZFCSyntax

/-- The literal enumerator program, simplified by the proved optimizer. -/
def program : ScalarPRCode.Realizes haltingTest := DirectEnumerator.program.optimize

/-- Closed representation of the enumerator reaching a halted state. -/
def representation : Rep Empty (fun _ => ∃ t, haltingTest t = 1) :=
  GraphRep.existsValue program.graphRep 1

/-- The nine-variable equation. -/
def expression : Expr (Fin 9) := CompactedJones.expression representation

end DiophantineConsistency.ExplicitZFCSyntax
