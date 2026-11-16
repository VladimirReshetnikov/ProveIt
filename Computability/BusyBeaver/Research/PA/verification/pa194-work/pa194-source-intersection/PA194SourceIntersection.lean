import PA194SourceSeparation
import PA194SourceAdjunctionConditional
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND
abbrev Term (n : Nat) := Semiterm language Nat n
abbrev Formula (n : Nat) := Semiproposition language n
def intersection (a s c : Term n) : Formula n :=
  .all (sourceIff (mem (Rew.bShift c) (.bvar 0))
    (.and (mem (Rew.bShift s) (.bvar 0)) (mem (Rew.bShift a) (.bvar 0))))
def intersectionProperty (a : Term 0) : Formula 1 := mem (Rew.bShift a) (.bvar 0)
def intersectionFormula : Form :=
  .all (.all (.exs (intersection (.bvar 2) (.bvar 1) (.bvar 0))))
def intersectionEnvironment (lo i : Nat) : Nat := if i = 0 then lo else 0
end M6.PA.RelationalSource.Ordinal
namespace PA194Logic.Relational.Source.Ordinal
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.ND
open PA194Logic PA194Logic.Relational

def intersectionAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hz : lo+4 ≤ z) :
    Derivation (Source.code intersectionFormula f lo z) := by
  have d := Source.separationSupplier (intersectionProperty (.fvar 0))
    (intersectionEnvironment lo) (lo+1) z (by omega)
    (by intro i; simp [intersectionEnvironment]; split <;> omega)
    (by simp [intersectionProperty,mem,depth]; omega)
  exact .all lo d
#print axioms intersectionAxiomSupplier
end PA194Logic.Relational.Source.Ordinal
