module
public import M6PA.Calibration.PAInterpretedFunctionCongruenceContext
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceEquality
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.PAForwardRelationalArithmeticClosure
public import PA196.Logic.Relational.Suppliers.PAForwardRelationalCoherenceSupplier
public import PA196.Logic.Relational.Suppliers.RelationalMultiplicationClosedResult
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

def functionCongruenceAxiomSupplier (labels : Nat → Nat) (lo z : Nat)
    (B : FunctionCongruenceBudgets labels lo z) (p : Form) (hp : p ∈ functionCongruenceAxioms) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code p labels lo z) := by
  classical
  by_cases hc : p ∈ coherenceAxioms
  · exact PA196.Logic.Relational.ForwardRelational.coherenceAxiomSupplier labels lo z B.positive B.labels (by have := B.room; omega)
      B.strictEntry B.domainEntry B.addCoherenceSep B.mulCoherenceSep
      (by have := B.adjunction; omega) B.addCoherence B.mulCoherence p hc
  have ht : p ∈ totalityAxioms := (List.mem_append.mp hp).resolve_left hc
  by_cases hr : p = reflexivityFormula
  · subst p; exact PA196.Logic.Relational.Source.reflexivitySupplier labels lo z
  by_cases hz : p = zeroInhabited
  · subst p
    exact PA196.Logic.Relational.ForwardRelational.zeroInhabitedSupplier labels lo z B.positive B.labels (by have := B.room; omega) B.zero
  by_cases hs : p = successorClosed
  · subst p
    exact PA196.Logic.Relational.ForwardRelational.successorClosedSupplier labels lo z B.positive B.labels B.room B.adjunction B.successor
  by_cases ha : p = addClosedResult
  · subst p
    exact PA196.Logic.Relational.Source.PairGraph.addClosedResultSupplier labels lo z B.positive B.labels B.room B.addTotalSep B.adjunction B.addTotal
  have hm : p = mulClosedResult := by simpa [totalityAxioms,hr,hz,hs,ha] using ht
  subst p
  exact PA196.Logic.Relational.Source.PairGraph.mulClosedResultSupplier labels lo z B.positive B.labels B.room B.mulTotalSep B.addTotalSep
    B.adjunction B.mulTotal
#print axioms functionCongruenceAxiomSupplier
end PA196.Logic.Relational.ForwardRelational
end
