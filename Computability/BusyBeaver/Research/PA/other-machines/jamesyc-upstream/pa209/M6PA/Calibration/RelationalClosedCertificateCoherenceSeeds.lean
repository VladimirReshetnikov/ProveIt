module
public import M6PA.Theory
public import M6PA.Calibration.RelationalClosedCertificateCoherenceSupport
public import M6PA.Calibration.PAInterpretedBudgetBounds
@[expose] public section
namespace M6.PA.RelationalClosedCertificate
noncomputable section
open FFL FFL.FirstOrder RelationalSource ND PairGraph ForwardRelational
attribute [local irreducible] functionBudgetBound lkBudget depth
  orderIsoReflexivityStatement isoSymmetryClosed isoTransitivityClosed addCoherenceStatement mulCoherenceStatement

def coherenceReserve (q : Form) : Nat := (max (functionBudgetBound 1) (max (1+6+1) (max (1+3+depth (∼identityProperty)) (max (1+2+lkBudget adjunctionDerivation) (max (1+lkBudget orderIsoReflexivityDerivation) (max (1+8+1) (max (1+6+depth (∼inverseProperty 0 (1+1))) (max (1+4+lkBudget adjunctionDerivation) (max (1+2+lkBudget (inverseSymmetryDerivation 1 0)) (max (1+9+1) (max (1+8+depth (∼compositionProperty 1 0 (2+1+1))) (max (1+5+lkBudget adjunctionDerivation) (max (1+3+lkBudget (compositionTransitivityDerivation 2 1 0)) (0)))))))))))))) + (1+Encodable.encode q)
theorem coherenceReserve_code (q : Form) : 1+Encodable.encode q≤coherenceReserve q := Nat.le_add_left _ _
theorem reserve_bound0 (q : Form) : functionBudgetBound 1 ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)
theorem reserve_bound1 (q : Form) : 1+6+1 ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound2 (q : Form) : 1+3+depth (∼identityProperty) ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound3 (q : Form) : 1+2+lkBudget adjunctionDerivation ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound4 (q : Form) : 1+lkBudget orderIsoReflexivityDerivation ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound5 (q : Form) : 1+8+1 ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound6 (q : Form) : 1+6+depth (∼inverseProperty 0 (1+1)) ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound7 (q : Form) : 1+4+lkBudget adjunctionDerivation ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound8 (q : Form) : 1+2+lkBudget (inverseSymmetryDerivation 1 0) ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound9 (q : Form) : 1+9+1 ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound10 (q : Form) : 1+8+depth (∼compositionProperty 1 0 (2+1+1)) ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound11 (q : Form) : 1+5+lkBudget adjunctionDerivation ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
theorem reserve_bound12 (q : Form) : 1+3+lkBudget (compositionTransitivityDerivation 2 1 0) ≤ coherenceReserve q := by
  unfold coherenceReserve
  exact le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)) (Nat.le_add_right _ _)
attribute [local irreducible] coherenceReserve
theorem coherence_budgets (q : Form) : FunctionCongruenceBudgets (fun _=>0) 1 (coherenceReserve q) :=
  FunctionCongruenceBudgets.of_bound _ _ _ (by decide) (by intro; decide) (reserve_bound0 q)
def isoReflexivityNativeProof : NativeCalculus.ActualBasis.Proof
    (code orderIsoReflexivityStatement (fun _=>0) 1 (coherenceReserve orderIsoReflexivityStatement)) :=
  orderIsoReflexivitySupplier _ _ _ (by decide) (by intro; decide)
    (lt_of_lt_of_le (Nat.lt_succ_self _) (reserve_bound1 _))
    (reserve_bound2 _) (reserve_bound3 _) (reserve_bound4 _)
def isoSymmetryNativeProof : NativeCalculus.ActualBasis.Proof
    (code isoSymmetryClosed (fun _=>0) 1 (coherenceReserve isoSymmetryClosed)) :=
  isoSymmetryClosedSupplier _ _ _ (by decide) (by intro; decide)
    (lt_of_lt_of_le (Nat.lt_succ_self _) (reserve_bound5 _))
    (reserve_bound6 _) (reserve_bound7 _) (reserve_bound8 _)
def isoTransitivityNativeProof : NativeCalculus.ActualBasis.Proof
    (code isoTransitivityClosed (fun _=>0) 1 (coherenceReserve isoTransitivityClosed)) :=
  isoTransitivityClosedSupplier _ _ _ (by decide) (by intro; decide)
    (lt_of_lt_of_le (Nat.lt_succ_self _) (reserve_bound9 _))
    (reserve_bound10 _) (reserve_bound11 _) (reserve_bound12 _)
def addCoherenceNativeProof : NativeCalculus.ActualBasis.Proof
    (code addCoherenceStatement (fun _=>0) 1 (coherenceReserve addCoherenceStatement)) := by
  have B := coherence_budgets addCoherenceStatement
  exact addCoherenceSupplier _ _ _ B.positive B.labels (by have := B.room; omega)
    B.strictEntry B.domainEntry B.addCoherenceSep (by have := B.adjunction; omega) B.addCoherence
def mulCoherenceNativeProof : NativeCalculus.ActualBasis.Proof
    (code mulCoherenceStatement (fun _=>0) 1 (coherenceReserve mulCoherenceStatement)) := by
  have B := coherence_budgets mulCoherenceStatement
  exact mulCoherenceSupplier _ _ _ B.positive B.labels (by have := B.room; omega)
    B.strictEntry B.domainEntry B.addCoherenceSep B.addCoherence B.mulCoherenceSep
    (by have := B.adjunction; omega) B.mulCoherence
#print axioms isoReflexivityNativeProof
#print axioms isoSymmetryNativeProof
#print axioms isoTransitivityNativeProof
#print axioms addCoherenceNativeProof
#print axioms mulCoherenceNativeProof
end
end M6.PA.RelationalClosedCertificate
