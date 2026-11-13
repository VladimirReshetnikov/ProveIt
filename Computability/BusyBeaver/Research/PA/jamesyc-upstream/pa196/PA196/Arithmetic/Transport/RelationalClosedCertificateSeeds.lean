module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeLanguage
public import PA196.Logic.Relational.Suppliers.RelationalMultiplicationUniversalOutput
public import PA196.Logic.Relational.Suppliers.PAForwardRelationalArithmeticClosure
public import M6PA.Calibration.PAInterpretedBudgetBounds
@[expose] public section

/-! Four actual external primitive totality proofs at symbolic standard
reserves. No large numeral certificate is evaluated or postulated. -/
namespace PA196.Arithmetic.Transport.RelationalClosedCertificate
noncomputable section
open FFL FFL.FirstOrder
open M6.PA M6.PA.RelationalSource M6.PA.RelationalSource.ND
open M6.PA.ForwardRelational M6.PA.RelationalSource.PairGraph

attribute [local irreducible] functionBudgetBound lkBudget mulUniversalOutputDerivation
  zeroInhabited successorClosed addClosedResult mulUniversalOutput

def primitiveReserve (q : Form) : Nat :=
  functionBudgetBound 1 + (1+lkBudget mulUniversalOutputDerivation) + (1+Encodable.encode q)
theorem primitiveReserve_code_bound (q : Form) : 1+Encodable.encode q≤primitiveReserve q := by
  exact Nat.le_add_left _ _
theorem primitiveReserve_mul_bound (q : Form) : 1+lkBudget mulUniversalOutputDerivation≤primitiveReserve q := by
  exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
attribute [local irreducible] primitiveReserve
theorem primitive_budgets (q : Form) : FunctionCongruenceBudgets (fun _=>0) 1 (primitiveReserve q) :=
  FunctionCongruenceBudgets.of_bound _ _ _ (by decide) (by intro; decide) (by unfold primitiveReserve; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

def zeroNativeProof : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code zeroInhabited (fun _=>0) 1 (primitiveReserve zeroInhabited)) := by
  have B := primitive_budgets zeroInhabited
  exact PA196.Logic.Relational.ForwardRelational.zeroInhabitedSupplier _ _ _ B.positive B.labels (Nat.lt_trans (by decide : 1+1<1+7) B.room) B.zero

def successorNativeProof : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code successorClosed (fun _=>0) 1 (primitiveReserve successorClosed)) := by
  have B := primitive_budgets successorClosed
  exact PA196.Logic.Relational.ForwardRelational.successorClosedSupplier _ _ _ B.positive B.labels B.room B.adjunction B.successor

def additionNativeProof : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code addClosedResult (fun _=>0) 1 (primitiveReserve addClosedResult)) := by
  have B := primitive_budgets addClosedResult
  exact PA196.Logic.Relational.Source.PairGraph.addClosedResultSupplier _ _ _ B.positive B.labels B.room B.addTotalSep B.adjunction B.addTotal

def multiplicationNativeProof : PA196.Logic.Derivation (PA196.Logic.Relational.Source.code mulUniversalOutput (fun _=>0) 1 (primitiveReserve mulUniversalOutput)) := by
  have B := primitive_budgets mulUniversalOutput
  exact PA196.Logic.Relational.Source.PairGraph.mulUniversalOutputSupplier _ _ _ B.positive B.labels B.room B.mulTotalSep B.addTotalSep B.adjunction B.mulTotal
    (primitiveReserve_mul_bound _)

#print axioms primitiveReserve_code_bound
#print axioms primitiveReserve_mul_bound
#print axioms zeroNativeProof
#print axioms successorNativeProof
#print axioms additionNativeProof
#print axioms multiplicationNativeProof
end
end PA196.Arithmetic.Transport.RelationalClosedCertificate

