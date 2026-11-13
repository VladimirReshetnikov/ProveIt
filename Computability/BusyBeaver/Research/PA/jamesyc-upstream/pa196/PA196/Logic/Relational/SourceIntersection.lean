module
public import PA196.Logic.Relational.SourceSeparation
public import M6PA.Calibration.RelationalOrdinalIntersectionAxiom
@[expose] public section
namespace PA196.Logic.Relational.Source.Ordinal
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.ND
open PA196.Logic PA196.Logic.Relational

def intersectionAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hz : lo+4 ≤ z) :
    Derivation (Source.code intersectionFormula f lo z) := by
  have d := Source.separationSupplier (intersectionProperty (.fvar 0))
    (intersectionEnvironment lo) (lo+1) z (by omega)
    (by intro i; simp [intersectionEnvironment]; split <;> omega)
    (by simp [intersectionProperty,mem,depth]; omega)
  exact .all lo d

#print axioms intersectionAxiomSupplier
end PA196.Logic.Relational.Source.Ordinal
