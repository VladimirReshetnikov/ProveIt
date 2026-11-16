module
public import M6PA.Calibration.PAForwardRelationalArithmeticClosure
public import PA196.Logic.Relational.SourceAdjunction
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.SourceContext
public import PA196.Logic.Relational.SourceIntersection
public import PA196.Logic.Relational.Suppliers.RelationalAdditionResultSupplier
public import PA196.Logic.Relational.Suppliers.RelationalOrdinalSuccessor
public import PA196.Logic.Relational.Suppliers.RelationalParameterClosure
public import PA196.Logic.Relational.Suppliers.RelationalSourceEmpty
@[expose] public section

/-! New PA196 certificates for the original finite source proof templates.
Only native supplier outputs are retargeted; source formulas, Foundation LK
derivations and numeric resource bounds are imported unchanged. -/
noncomputable section

namespace PA196.Logic.Relational.Source.PairGraph
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.RelationalSource.PairGraph
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder ND

def addClosedResultSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+7 < z)
    (hsep : lo+4+depth (∼prefixProperty 0) ≤ z)
    (hadj : lo+3+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+1+lkBudget (addTotalDerivation 0) ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code addClosedResult f lo z) := by
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.PairGraph.addTotalSupplier 0 (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega
  · omega
  · omega
  · omega
#print axioms addClosedResultSupplier
end PA196.Logic.Relational.Source.PairGraph

namespace PA196.Logic.Relational.ForwardRelational
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.ForwardRelational
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder ND
open FFL FFL.FirstOrder M6.PA.RelationalSource ND

def successorClosedSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+7 < z)
    (hadj : lo+3+lkBudget adjunctionDerivation ≤ z)
    (hbudget : lo+1+lkBudget (Ordinal.domainSuccessorDerivation (.fvar 0)) ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code successorClosed f lo z) := by
  apply PA196.Logic.Relational.Source.closeParameterSupplier
  apply PA196.Logic.Relational.Source.Ordinal.domainSuccessorSupplier (.fvar 0) (shiftedLabels f lo) (lo+1) z (by omega)
  · intro i
    cases i with
    | zero => simp [shiftedLabels]
    | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  · omega
  · omega
  · omega
#print axioms successorClosedSupplier
end PA196.Logic.Relational.ForwardRelational

namespace PA196.Logic.Relational.ForwardRelational
open FFL FFL.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.ForwardRelational
open PA196.Logic PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
open FFL FFL.FirstOrder ND
open FFL FFL.FirstOrder M6.PA.RelationalSource ND

def zeroInhabitedSupplier (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i, f i < lo) (hz : lo+1 < z)
    (hbudget : lo+lkBudget zeroInhabitedDerivation ≤ z) :
    PA196.Logic.Derivation (PA196.Logic.Relational.Source.code zeroInhabited f lo z) := by
  apply PA196.Logic.Relational.Source.compileContext [emptyFormula] _ zeroInhabitedDerivation f lo z hlo hf hbudget
  intro p hp
  have he : p = emptyFormula := by simpa using hp
  subst p
  exact PA196.Logic.Relational.Source.emptySupplier f lo z hz
#print axioms zeroInhabitedSupplier
end PA196.Logic.Relational.ForwardRelational
end
