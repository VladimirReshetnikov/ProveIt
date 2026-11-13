module
public import PA196.Arithmetic.Certificates.MPGen
@[expose] public section
open M6.PA
namespace PA196.Arithmetic.Certificates
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA.SourceCantorInternal Scalar CheckerRule Checker HeadGraphs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def pack4Value (a b c u : V) : V := pairValue a (pack3Value b c u)
noncomputable def leafCertificate (tag payload : V) : V :=
  pairValue 1 (pairValue tag payload)

theorem verify_leaf (tag payload out : V)
    (h : ∀ previous : V, ruleValue previous tag payload = out+1) :
    verifyValue (leafCertificate tag payload) = out+1 := by
  simp only [leafCertificate,verifyValue,pair_left,pair_right]
  rw [show (1:V)=0+1 by simp,table_succ,
    CheckerRows.rows_nth _ _ _ (lt_add_one _)]
  simp only [pair_left,pair_right]
  simpa using h (tableValue 0 (pairValue tag payload))

theorem verify_head1 (a b : V) :
    verifyValue (leafCertificate 2 (pack2Value a b)) =
      M6.PA.ActualArithmeticGraph.eval head1Expr a b 0 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf1
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack3Value,pack2Value]
  rfl

theorem verify_head2 (a b c : V) :
    verifyValue (leafCertificate 3 (pack3Value a b c)) =
      M6.PA.ActualArithmeticGraph.eval head2Expr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf2
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack3Value,pack2Value]
  rfl

theorem verify_head3 (a b c : V) :
    verifyValue (leafCertificate 4 (pack3Value a b c)) =
      M6.PA.ActualArithmeticGraph.eval head3Expr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf3
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack3Value,pack2Value]
  rfl

theorem verify_head4 (a b c : V) :
    verifyValue (leafCertificate 5 (pack3Value a b c)) =
      M6.PA.ActualArithmeticGraph.eval head4Expr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf4
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack3Value,pack2Value]
  rfl

theorem verify_head5 (a b : V) :
    verifyValue (leafCertificate 6 (pack2Value a b)) =
      M6.PA.ActualArithmeticGraph.eval head5Expr a b 0 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf5
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack3Value,pack2Value]
  rfl

theorem verify_head6 (a b c : V) :
    verifyValue (leafCertificate 7 (pack3Value a b c)) =
      M6.PA.ActualArithmeticGraph.eval head6Expr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf6
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack3Value,pack2Value]
  rfl

theorem verify_r8 (a b c u : V) (hu : u ≤ a) :
    verifyValue (leafCertificate 8 (pack4Value a b c u)) =
      M6.PA.ActualArithmeticGraph.eval rho8Expr a b c u+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold leaf8
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack4Value,pack3Value,pack2Value,hu]

theorem verify_bundle (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    verifyValue (leafCertificate 9 (pack3Value a b c)) =
      M6.PA.ActualArithmeticGraph.eval bundleExpr a b c 0+1 := by
  apply verify_leaf
  intro previous
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  norm_num
  unfold rawBundle
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack3Value,pack2Value,hca,hcb]
  rfl

#print axioms verify_head1
#print axioms verify_head6
#print axioms verify_r8
#print axioms verify_bundle
end PA196.Arithmetic.Certificates
