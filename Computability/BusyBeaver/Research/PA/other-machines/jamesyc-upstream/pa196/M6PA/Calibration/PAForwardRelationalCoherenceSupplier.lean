module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalCoherenceGuarded
@[expose] public section

/-! Actual-basis compilation with all eight closed premises paid. Environment
isomorphisms and the two real value relations remain explicit finite implication
guards. The distinct arithmetic Separation requirements are preserved. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def coherenceAxiomSupplier (labels : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hlabels : ∀ i, labels i < lo) (hz : lo+6 < z)
    (hstrict : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (haddsep : lo+3+depth (∼addCoherenceProperty) ≤ z)
    (hmulsep : lo+3+depth (∼mulCoherenceProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (haddbudget : lo+lkBudget addCoherenceDerivation ≤ z)
    (hmulbudget : lo+lkBudget mulCoherenceDerivation ≤ z)
    (p : Form) (hp : p ∈ coherenceAxioms) :
    NativeCalculus.ActualBasis.Proof (code p labels lo z) := by
  classical
  by_cases h0 : p = reflexivityFormula
  · subst p; exact reflexivitySupplier labels lo z
  by_cases h1 : p = symmetryFormula
  · subst p; exact symmetrySupplier labels lo z
  by_cases h2 : p = transitivityFormula
  · subst p; exact transitivitySupplier labels lo z
  by_cases h3 : p = congruenceFormula
  · subst p; exact congruenceSupplier labels lo z (by omega)
  by_cases h4 : p = emptyFormula
  · subst p; exact emptySupplier labels lo z (by omega)
  by_cases h5 : p = adjunctionFormula
  · subst p; exact adjunctionSupplier labels lo z hlo hz hadj
  by_cases h6 : p = addCoherenceStatement
  · subst p
    exact addCoherenceSupplier labels lo z hlo hlabels hz hstrict hinclusive haddsep hadj haddbudget
  have h7 : p = mulCoherenceStatement := by
    simpa [coherenceAxioms,h0,h1,h2,h3,h4,h5,h6] using hp
  subst p
  exact mulCoherenceSupplier labels lo z hlo hlabels hz hstrict hinclusive
    haddsep haddbudget hmulsep hadj hmulbudget

def guardedCoherenceSupplier {n : Nat} (t : SourceTerm n)
    (b b' : Fin n → Term 0) (f f' : Nat → Term 0) (r s : Term 0)
    (labels : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hlabels : ∀ i, labels i < lo) (hz : lo+6 < z)
    (hstrict : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (hinclusive : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z)
    (haddsep : lo+3+depth (∼addCoherenceProperty) ≤ z)
    (hmulsep : lo+3+depth (∼mulCoherenceProperty) ≤ z)
    (hadj : lo+2+lkBudget adjunctionDerivation ≤ z)
    (haddbudget : lo+lkBudget addCoherenceDerivation ≤ z)
    (hmulbudget : lo+lkBudget mulCoherenceDerivation ≤ z)
    (hbudget : lo+lkBudget (guardedCoherenceDerivation t b b' f f' r s) ≤ z) :
    NativeCalculus.ActualBasis.Proof
      (code (guardedCoherenceStatement t b b' f f' r s) labels lo z) :=
  compileContext coherenceAxioms _ (guardedCoherenceDerivation t b b' f f' r s)
    labels lo z hlo hlabels hbudget
    (coherenceAxiomSupplier labels lo z hlo hlabels hz hstrict hinclusive
      haddsep hmulsep hadj haddbudget hmulbudget)

#print axioms coherenceAxiomSupplier
#print axioms guardedCoherenceSupplier
end M6.PA.ForwardRelational
