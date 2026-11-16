module
public import M6PA.Calibration.PAForwardRelationalCoherenceSupplier
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceEquality
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.RelationalAdditionCoherenceSupplier
public import PA196.Logic.Relational.Suppliers.RelationalMultiplicationCoherenceSupplier
public import PA196.Logic.Relational.Suppliers.RelationalSourceEmpty
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
open M6.PA.RelationalSource.Ordinal (Term Formula)
open M6.PA.RelationalSource.PairGraph

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
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code p labels lo z) := by
  classical
  by_cases h0 : p = reflexivityFormula
  · subst p; exact PA196.Logic.Relational.Source.reflexivitySupplier labels lo z
  by_cases h1 : p = symmetryFormula
  · subst p; exact PA196.Logic.Relational.Source.symmetrySupplier labels lo z
  by_cases h2 : p = transitivityFormula
  · subst p; exact PA196.Logic.Relational.Source.transitivitySupplier labels lo z
  by_cases h3 : p = congruenceFormula
  · subst p; exact PA196.Logic.Relational.Source.congruenceSupplier labels lo z (by omega)
  by_cases h4 : p = emptyFormula
  · subst p; exact PA196.Logic.Relational.Source.emptySupplier labels lo z (by omega)
  by_cases h5 : p = adjunctionFormula
  · subst p; exact PA196.Logic.Relational.Source.adjunctionSupplier labels lo z hlo hz hadj
  by_cases h6 : p = addCoherenceStatement
  · subst p
    exact PA196.Logic.Relational.Source.PairGraph.addCoherenceSupplier labels lo z hlo hlabels hz hstrict hinclusive haddsep hadj haddbudget
  have h7 : p = mulCoherenceStatement := by
    simpa [coherenceAxioms,h0,h1,h2,h3,h4,h5,h6] using hp
  subst p
  exact PA196.Logic.Relational.Source.PairGraph.mulCoherenceSupplier labels lo z hlo hlabels hz hstrict hinclusive
    haddsep haddbudget hmulsep hadj hmulbudget
#print axioms coherenceAxiomSupplier
end PA196.Logic.Relational.ForwardRelational

namespace PA196.Logic.Relational.ForwardRelational
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.ForwardRelational
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder M6.PA.RelationalSource ND
open M6.PA.RelationalSource.Ordinal (Term Formula)
open M6.PA.RelationalSource.PairGraph

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
    PA196.Logic.Derivation
      (PA196.Logic.Relational.Source.code (guardedCoherenceStatement t b b' f f' r s) labels lo z) :=
  PA196.Logic.Relational.Source.compileContext coherenceAxioms _ (guardedCoherenceDerivation t b b' f f' r s)
    labels lo z hlo hlabels hbudget
    (PA196.Logic.Relational.ForwardRelational.coherenceAxiomSupplier labels lo z hlo hlabels hz hstrict hinclusive
      haddsep hmulsep hadj haddbudget hmulbudget)
#print axioms guardedCoherenceSupplier
end PA196.Logic.Relational.ForwardRelational
end
