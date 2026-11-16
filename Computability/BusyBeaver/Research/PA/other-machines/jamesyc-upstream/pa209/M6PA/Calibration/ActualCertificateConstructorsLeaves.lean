module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateConstructorsMPGen
@[expose] public section

/-! Exact numeric one-round V1 leaf certificates, including all guards. -/
namespace M6.PA.ActualCertificateConstructors
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open SourceCantorInternal ActualCheckExpression ActualRuleExpression
open ActualCheckerBlueprint ActualHeadGraphs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def pack4Value (a b c u : V) : V := pairValue a (pack3Value b c u)
noncomputable def leafCertificate (tag payload : V) : V :=
  pairValue 1 (pairValue tag payload)

/-- A successful exact rule at the zero table is already a one-round certificate. -/
theorem verify_leaf (tag payload out : V)
    (h : ∀ previous : V, ruleValue previous tag payload = out+1) :
    verifyValue (leafCertificate tag payload) = out+1 := by
  simp only [leafCertificate,verifyValue,pair_left,pair_right]
  rw [show (1:V)=0+1 by simp,table_succ,
    ActualCheckerRows.rows_nth _ _ _ (lt_add_one _)]
  simp only [pair_left,pair_right]
  simpa using h (tableValue 0 (pairValue tag payload))

theorem verify_r1 (a b : V) :
    verifyValue (leafCertificate 2 (pack2Value a b)) =
      ActualArithmeticGraph.eval rho1Expr a b 0 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf1
  expose_actual_rule_helpers
  simp [ActualCheckExpression.eval,pack2Value]
  rfl

theorem verify_r2 (a b c : V) :
    verifyValue (leafCertificate 3 (pack3Value a b c)) =
      ActualArithmeticGraph.eval rho2Expr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf2
  expose_actual_rule_helpers
  simp [ActualCheckExpression.eval,pack3Value,pack2Value]
  rfl

theorem verify_r3 (a b c : V) :
    verifyValue (leafCertificate 4 (pack3Value a b c)) =
      ActualArithmeticGraph.eval rho3Expr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf3
  expose_actual_rule_helpers
  simp [ActualCheckExpression.eval,pack3Value,pack2Value]
  rfl

theorem verify_r4 (a b c : V) :
    verifyValue (leafCertificate 5 (pack3Value a b c)) =
      ActualArithmeticGraph.eval rho4Expr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf4
  expose_actual_rule_helpers
  simp [ActualCheckExpression.eval,pack3Value,pack2Value]
  rfl

theorem verify_r5 (a b c : V) :
    verifyValue (leafCertificate 6 (pack3Value a b c)) =
      ActualArithmeticGraph.eval rho5Expr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf5
  expose_actual_rule_helpers
  simp [ActualCheckExpression.eval,pack3Value,pack2Value]
  rfl

theorem verify_r6 (a b : V) :
    verifyValue (leafCertificate 7 (pack2Value a b)) =
      ActualArithmeticGraph.eval rho6Expr a b 0 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf6
  expose_actual_rule_helpers
  simp [ActualCheckExpression.eval,pack2Value]

theorem verify_r7 (a b c : V) :
    verifyValue (leafCertificate 8 (pack3Value a b c)) =
      ActualArithmeticGraph.eval rho7Expr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf7
  expose_actual_rule_helpers
  simp [ActualCheckExpression.eval,pack3Value,pack2Value]
  rfl

theorem verify_r8 (a b c u : V) (hu : u ≤ a) :
    verifyValue (leafCertificate 9 (pack4Value a b c u)) =
      ActualArithmeticGraph.eval rho8Expr a b c u+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf8
  expose_actual_rule_helpers
  simp [ActualCheckExpression.eval,pack4Value,pack3Value,pack2Value,hu]

theorem verify_bundle (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    verifyValue (leafCertificate 10 (pack3Value a b c)) =
      ActualArithmeticGraph.eval bundleExpr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [ActualCheckExpression.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold rawBundle
  expose_actual_rule_helpers
  simp [ActualCheckExpression.eval,pack3Value,pack2Value,hca,hcb]
  rfl

#print axioms verify_r1
#print axioms verify_r2
#print axioms verify_r3
#print axioms verify_r4
#print axioms verify_r5
#print axioms verify_r6
#print axioms verify_r7
#print axioms verify_r8
#print axioms verify_bundle
#print axioms verify_leaf
end M6.PA.ActualCertificateConstructors

