module
public import M6PA.Calibration.RelationalParameterClosure
public import PA196.Logic.Relational.Encoding
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.SourceSeparation
@[expose] public section

/-! New PA196 certificates for the original finite source proof templates.
Only native supplier outputs are retargeted; source formulas, Foundation LK
derivations and numeric resource bounds are imported unchanged. -/
noncomputable section

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder  PA196.Logic.Relational

def closeParameterSupplier (p : Proposition language) (f : Nat → Nat) (lo z : Nat)
    (d : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code p (shiftedLabels f lo) (lo+1) z)) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (closeParameter p) f lo z) := by
  simpa only [PA196.Logic.Relational.Source.code,closeParameter,toNamed,PA196.Logic.Relational.relationalCode,toNamed_fixParameter] using
    (PA196.Logic.Derivation.all lo d)
#print axioms closeParameterSupplier
end PA196.Logic.Relational.Source

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder  PA196.Logic.Relational

def closedSeparationSupplier (p : Semiproposition language 1) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i,f i < lo) (hz : lo+4+depth p ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code (closeParameter (separationFormula p)) f lo z) := by
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.separationSupplier p (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega
#print axioms closedSeparationSupplier
end PA196.Logic.Relational.Source
end
