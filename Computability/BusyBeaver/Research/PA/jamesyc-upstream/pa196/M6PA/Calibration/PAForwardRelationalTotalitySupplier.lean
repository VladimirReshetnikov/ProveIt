module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalTotalityContext
@[expose] public section

/-! Compilation to the actual basis pays every closed arithmetic premise.
Only the explicitly named, finitely indexed environment-domain suppliers
remain open. No numerical coding of arbitrary host environments is asserted. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)

/-- Finite syntactic lookup only; no semantic representative is chosen. -/
def environmentContextSupplier (xs : List (Term 0)) (labels : Nat → Nat) (lo z : Nat)
    (suppliers : ∀ x, x ∈ xs →
      NativeCalculus.ActualBasis.Proof (code (Ordinal.domain x) labels lo z))
    (p : Form) (hp : p ∈ xs.map Ordinal.domain) :
    NativeCalculus.ActualBasis.Proof (code p labels lo z) := by
  classical
  cases xs with
  | nil => exact False.elim (by simpa using hp)
  | cons x xs =>
    by_cases he : p = Ordinal.domain x
    · subst p
      exact suppliers x (by simp)
    · apply environmentContextSupplier xs labels lo z
        (fun y hy => suppliers y (by simp [hy])) p
      simpa [eq_comm,he] using hp

def termTotalitySupplier {n : Nat} (t : SourceTerm n)
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
    (htermBudget : lo+lkBudget (termTotalityDerivation t b f) ≤ z)
    (environmentSuppliers : ∀ x, x ∈ environmentInputs b f t →
      NativeCalculus.ActualBasis.Proof (code (Ordinal.domain x) labels lo z)) :
    NativeCalculus.ActualBasis.Proof (code (hasValue t b f) labels lo z) := by
  apply compileContext (totalityContext t b f) _ (termTotalityDerivation t b f)
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
  by_cases hm : p = PairGraph.mulClosedResult
  · subst p; exact PairGraph.mulClosedResultSupplier labels lo z hlo hlabels hz hmulSep haddSep hadj hmulBudget
  have hd : p ∈ (environmentInputs b f t).map Ordinal.domain := by
    simpa [totalityContext,totalityAxioms,hr,hzero,hs,ha,hm] using hp
  exact environmentContextSupplier _ labels lo z environmentSuppliers p hd

#print axioms environmentContextSupplier
#print axioms termTotalitySupplier
end M6.PA.ForwardRelational
