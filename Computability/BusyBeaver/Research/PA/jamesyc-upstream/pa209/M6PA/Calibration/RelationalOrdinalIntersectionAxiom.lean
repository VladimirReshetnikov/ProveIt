module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrdinalIntersection
@[expose] public section

/-! The fixed universally closed intersection axiom is an actual Separation
instance, generalized at the numeric proof level. The allocated name of the
first argument is strictly below the allocator for the remaining binders. -/
namespace M6.PA.RelationalSource.Ordinal
open FFL FFL.FirstOrder ND

def intersectionFormula : Form :=
  ∀¹ ∀¹ ∃¹ intersection (.bvar 2) (.bvar 1) (.bvar 0)

def intersectionEnvironment (lo i : Nat) : Nat := if i = 0 then lo else 0

def intersectionAxiomSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hz : lo+4 ≤ z) :
    NativeCalculus.ActualBasis.Proof (code intersectionFormula f lo z) := by
  have d := separationSupplier (intersectionProperty (.fvar 0))
    (intersectionEnvironment lo) (lo+1) z (by omega)
    (by intro i; simp [intersectionEnvironment]; split <;> omega)
    (by simp [intersectionProperty,mem,depth]; omega)
  exact .all lo d

/-- The fixed axiom specializes to arbitrary arguments without any name
freshness restriction on their free parameters. -/
def intersectionFromAxiom {Γ : List Form} (a s : Term 0)
    (d : ND.Proof Γ intersectionFormula) : ND.Proof Γ (intersectionExists a s) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    cases s with
    | bvar j => nomatch j
    | func f _ => nomatch f
    | fvar j =>
      have h := allElim _ (.fvar j) (allElim _ (.fvar i) d)
      convert h using 1 ; intersectionSyntax

#print axioms intersectionAxiomSupplier
#print axioms intersectionFromAxiom
end M6.PA.RelationalSource.Ordinal
