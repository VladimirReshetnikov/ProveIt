module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalTotalitySupplier
@[expose] public section

/-! Discharging the finite domain assumptions into explicit implication guards.
Unlike the pointwise supplier, the guarded supplier has no open environment
supplier premise. This is still typed finite syntax, not an internal compiler. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

/-- Guards are discharged from the head, so the final implication order is
reverse list order. Repeated occurrences are harmless and retained. -/
def guardContext : List Form → Form → Form
  | [], p => p
  | q :: qs, p => guardContext qs (q 🡒 p)

def dischargeContext (Δ : List Form) {Γ : List Form} (p : Form)
    (h : ND.Proof (Δ ++ Γ) p) : ND.Proof Γ (guardContext Δ p) := by
  cases Δ with
  | nil => exact h
  | cons q qs => exact dischargeContext qs (q 🡒 p) (impIntro h)

def guardedTermStatement {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) : Form :=
  guardContext ((environmentInputs b f t).map Ordinal.domain) (hasValue t b f)

def guardedTermDerivation {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) :
    ND.Proof totalityAxioms (guardedTermStatement t b f) := by
  apply dischargeContext
  apply weaken (termTotalityDerivation t b f)
  intro p hp
  simpa only [totalityContext,List.mem_append,or_comm] using hp

/-- All source premises of the guarded theorem are paid. The two Separation
budgets remain distinct and no domain assumption is silently erased. -/
def guardedTermSupplier {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0)
    (labels : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hlabels : ∀ i, labels i < lo) (hz : lo+7 < z)
    (haddSep : lo+4+depth (∼PairGraph.prefixProperty 0) ≤ z)
    (hmulSep : lo+4+depth (∼PairGraph.mulPrefixProperty 0) ≤ z)
    (hadj : lo+3+lkBudget adjunctionDerivation ≤ z)
    (hzeroBudget : lo+lkBudget zeroInhabitedDerivation ≤ z)
    (hsuccBudget : lo+1+lkBudget (Ordinal.domainSuccessorDerivation (.fvar 0)) ≤ z)
    (haddBudget : lo+1+lkBudget (PairGraph.addTotalDerivation 0) ≤ z)
    (hmulBudget : lo+1+lkBudget (PairGraph.mulTotalDerivation 0) ≤ z)
    (htermBudget : lo+lkBudget (guardedTermDerivation t b f) ≤ z) :
    NativeCalculus.ActualBasis.Proof (code (guardedTermStatement t b f) labels lo z) := by
  apply compileContext totalityAxioms _ (guardedTermDerivation t b f)
    labels lo z hlo hlabels htermBudget
  intro p hp
  classical
  by_cases hr : p = reflexivityFormula
  · subst p; exact reflexivitySupplier labels lo z
  by_cases hzero : p = zeroInhabited
  · subst p; exact zeroInhabitedSupplier labels lo z hlo hlabels (by omega) hzeroBudget
  by_cases hs : p = successorClosed
  · subst p; exact successorClosedSupplier labels lo z hlo hlabels hz hadj hsuccBudget
  by_cases ha : p = PairGraph.addClosedResult
  · subst p; exact PairGraph.addClosedResultSupplier labels lo z hlo hlabels hz haddSep hadj haddBudget
  have hm : p = PairGraph.mulClosedResult := by
    simpa [totalityAxioms,hr,hzero,hs,ha] using hp
  subst p
  exact PairGraph.mulClosedResultSupplier labels lo z hlo hlabels hz hmulSep haddSep hadj hmulBudget

#print axioms dischargeContext
#print axioms guardedTermDerivation
#print axioms guardedTermSupplier
end M6.PA.ForwardRelational
