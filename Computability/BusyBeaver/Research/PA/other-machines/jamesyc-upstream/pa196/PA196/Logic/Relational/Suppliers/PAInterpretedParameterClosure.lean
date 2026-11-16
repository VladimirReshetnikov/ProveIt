module
public import M6PA.Calibration.PAInterpretedParameterClosure
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.RelationalParameterClosure
@[expose] public section

/-! New PA196 certificates for the original finite source proof templates.
Only native supplier outputs are retargeted; source formulas, Foundation LK
derivations and numeric resource bounds are imported unchanged. -/
noncomputable section

namespace PA196.Logic.Relational.ForwardRelational
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.ForwardRelational
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder M6.PA.RelationalSource ND

def closeParametersSupplier (n : Nat) (p : Form) (f : Nat → Nat) (lo z : Nat)
    (d : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code p (closureLabels n f lo) (lo+n) z)) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (closeParameters n p) f lo z) := by
  induction n generalizing f lo with
  | zero => exact d
  | succ n ih =>
    apply PA196.Logic.Relational.Source.closeParameterSupplier
    apply ih (shiftedLabels f lo) (lo+1)
    simpa only [closureLabels,Nat.add_assoc,Nat.add_comm 1 n] using d
#print axioms closeParametersSupplier
end PA196.Logic.Relational.ForwardRelational
end
