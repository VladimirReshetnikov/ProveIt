module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFunctionCongruenceSuccImage
public import M6PA.Calibration.PAInterpretedFunctionCongruenceBinaryImage
public import M6PA.Calibration.PAForwardRelationalCoherenceSupplier
@[expose] public section

/-! One explicit finite context for the three function-congruence images.
Its ordinary equality, empty/adjunction and closed arithmetic premises are
listed, rather than silently inherited from a stronger set theory. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
open PairGraph

def functionCongruenceAxioms : List Form := coherenceAxioms ++ totalityAxioms

def functionCongruenceCoherence : CoherencePremises functionCongruenceAxioms :=
  coherencePremisesFromContext (fun _ h => List.mem_append_left _ h)

def functionCongruenceTotality : TotalityPremises functionCongruenceAxioms :=
  ⟨assumption (by simp [functionCongruenceAxioms,totalityAxioms]),
   assumption (by simp [functionCongruenceAxioms,totalityAxioms]),
   assumption (by simp [functionCongruenceAxioms,totalityAxioms]),
   assumption (by simp [functionCongruenceAxioms,totalityAxioms]),
   assumption (by simp [functionCongruenceAxioms,totalityAxioms])⟩

def succCongruenceDerivation (f : Nat → Term 0) :
    ND.Proof functionCongruenceAxioms (formula Presentation.succCongruence Fin.elim0 f) :=
  interpretedSuccCongruence functionCongruenceCoherence functionCongruenceTotality f

def addCongruenceDerivation (f : Nat → Term 0) :
    ND.Proof functionCongruenceAxioms (formula Presentation.addCongruence Fin.elim0 f) :=
  interpretedAddCongruence functionCongruenceCoherence functionCongruenceTotality f

def mulCongruenceDerivation (f : Nat → Term 0) :
    ND.Proof functionCongruenceAxioms (formula Presentation.mulCongruence Fin.elim0 f) :=
  interpretedMulCongruence functionCongruenceCoherence functionCongruenceTotality f

/-- Every field is an explicit numerical bound for an accepted supplier.
In particular all six distinct Separation budgets are retained separately. -/
structure FunctionCongruenceBudgets (labels : Nat → Nat) (lo z : Nat) : Prop where
  positive : 0 < lo
  labels : ∀ i, labels i < lo
  room : lo+7 < z
  strictEntry : lo+4+depth (strictEntryProperty (n := 0) (.fvar 0)) ≤ z
  domainEntry : lo+4+depth (domainEntryProperty (n := 0) (.fvar 0)) ≤ z
  addCoherenceSep : lo+3+depth (∼addCoherenceProperty) ≤ z
  mulCoherenceSep : lo+3+depth (∼mulCoherenceProperty) ≤ z
  addTotalSep : lo+4+depth (∼prefixProperty 0) ≤ z
  mulTotalSep : lo+4+depth (∼mulPrefixProperty 0) ≤ z
  adjunction : lo+3+lkBudget adjunctionDerivation ≤ z
  addCoherence : lo+lkBudget addCoherenceDerivation ≤ z
  mulCoherence : lo+lkBudget mulCoherenceDerivation ≤ z
  zero : lo+lkBudget zeroInhabitedDerivation ≤ z
  successor : lo+1+lkBudget (Ordinal.domainSuccessorDerivation (.fvar 0)) ≤ z
  addTotal : lo+1+lkBudget (addTotalDerivation 0) ≤ z
  mulTotal : lo+1+lkBudget (mulTotalDerivation 0) ≤ z

def functionCongruenceAxiomSupplier (labels : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets labels lo z) (p : Form) (hp : p ∈ functionCongruenceAxioms) :
    NativeCalculus.ActualBasis.Proof (code p labels lo z) := by
  classical
  by_cases hc : p ∈ coherenceAxioms
  · exact coherenceAxiomSupplier labels lo z B.positive B.labels (by have := B.room; omega)
      B.strictEntry B.domainEntry B.addCoherenceSep B.mulCoherenceSep
      (by have := B.adjunction; omega) B.addCoherence B.mulCoherence p hc
  have ht : p ∈ totalityAxioms := (List.mem_append.mp hp).resolve_left hc
  by_cases hr : p = reflexivityFormula
  · subst p; exact reflexivitySupplier labels lo z
  by_cases hz : p = zeroInhabited
  · subst p
    exact zeroInhabitedSupplier labels lo z B.positive B.labels (by have := B.room; omega) B.zero
  by_cases hs : p = successorClosed
  · subst p
    exact successorClosedSupplier labels lo z B.positive B.labels B.room B.adjunction B.successor
  by_cases ha : p = addClosedResult
  · subst p
    exact addClosedResultSupplier labels lo z B.positive B.labels B.room B.addTotalSep B.adjunction B.addTotal
  have hm : p = mulClosedResult := by simpa [totalityAxioms,hr,hz,hs,ha] using ht
  subst p
  exact mulClosedResultSupplier labels lo z B.positive B.labels B.room B.mulTotalSep B.addTotalSep
    B.adjunction B.mulTotal

#print axioms succCongruenceDerivation
#print axioms addCongruenceDerivation
#print axioms mulCongruenceDerivation
#print axioms functionCongruenceAxiomSupplier
end M6.PA.ForwardRelational
