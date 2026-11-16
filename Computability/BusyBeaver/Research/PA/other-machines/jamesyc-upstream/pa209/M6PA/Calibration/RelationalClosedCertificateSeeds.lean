module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalCodeLanguage
public import M6PA.Calibration.RelationalMultiplicationUniversalOutput
public import M6PA.Calibration.PAInterpretedBudgetBounds
@[expose] public section

/-! Four actual external primitive totality proofs at symbolic standard
reserves. No large numeral certificate is evaluated or postulated. -/
namespace M6.PA.RelationalClosedCertificate
noncomputable section
open FFL FFL.FirstOrder RelationalSource ND ForwardRelational PairGraph

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

def zeroNativeProof : NativeCalculus.ActualBasis.Proof (code zeroInhabited (fun _=>0) 1 (primitiveReserve zeroInhabited)) := by
  have B := primitive_budgets zeroInhabited
  exact zeroInhabitedSupplier _ _ _ B.positive B.labels (Nat.lt_trans (by decide : 1+1<1+7) B.room) B.zero

def successorNativeProof : NativeCalculus.ActualBasis.Proof (code successorClosed (fun _=>0) 1 (primitiveReserve successorClosed)) := by
  have B := primitive_budgets successorClosed
  exact successorClosedSupplier _ _ _ B.positive B.labels B.room B.adjunction B.successor

def additionNativeProof : NativeCalculus.ActualBasis.Proof (code addClosedResult (fun _=>0) 1 (primitiveReserve addClosedResult)) := by
  have B := primitive_budgets addClosedResult
  exact addClosedResultSupplier _ _ _ B.positive B.labels B.room B.addTotalSep B.adjunction B.addTotal

def multiplicationNativeProof : NativeCalculus.ActualBasis.Proof (code mulUniversalOutput (fun _=>0) 1 (primitiveReserve mulUniversalOutput)) := by
  have B := primitive_budgets mulUniversalOutput
  exact mulUniversalOutputSupplier _ _ _ B.positive B.labels B.room B.mulTotalSep B.addTotalSep B.adjunction B.mulTotal
    (primitiveReserve_mul_bound _)

#print axioms primitiveReserve_code_bound
#print axioms primitiveReserve_mul_bound
#print axioms zeroNativeProof
#print axioms successorNativeProof
#print axioms additionNativeProof
#print axioms multiplicationNativeProof
end
end M6.PA.RelationalClosedCertificate

