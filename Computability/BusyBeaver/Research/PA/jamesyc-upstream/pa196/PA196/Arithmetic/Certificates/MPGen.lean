module
public import M6PA.Theory
public import PA196.Arithmetic.Certificates.Fuel
@[expose] public section

/-! Explicit numeric PA196 MP and GEN certificates, correct uniformly in PA
models. These do not translate Foundation proof constructors by themselves. -/
open M6.PA
namespace PA196.Arithmetic.Certificates
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA.SourceCantorInternal Scalar CheckerRule
open Checker HeadGraphs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def pack2Value (a b : V) : V := pairValue a (pairValue b 0)
noncomputable def pack3Value (a b c : V) : V := pairValue a (pack2Value b c)
noncomputable def mpTree (b p q : V) : V := pairValue 0 (pack3Value b p q)
noncomputable def genTree (v p : V) : V := pairValue 1 (pack2Value v p)
noncomputable def implicationValue (a b : V) : V := M6.PA.ActualArithmeticGraph.eval implicationExpr a b 0 0
noncomputable def universalValue (v a : V) : V := M6.PA.ActualArithmeticGraph.eval universalExpr v a 0 0

@[simp] theorem pair_left (a b : V) : decodeLeft (pairValue a b)=a := (decode_pairValue a b).1
@[simp] theorem pair_right (a b : V) : decodeRight (pairValue a b)=b := (decode_pairValue a b).2

theorem successor_ne_zero (a : V) : a+1 ≠ 0 :=
  ne_of_gt (lt_of_le_of_lt (by simp : (0:V) ≤ a) (lt_add_one a))

theorem mp_rule (previous a b p q : V)
    (hp : nth previous p = a+1) (hq : nth previous q = implicationValue a b+1) :
    ruleValue previous 0 (pack3Value b p q) = b+1 := by
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,ite_true]
  unfold mp
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack3Value,pack2Value,hp,hq,
    implicationValue]

theorem gen_rule (previous v a p : V) (hp : nth previous p = a+1) :
    ruleValue previous 1 (pack2Value v p) = universalValue v a+1 := by
  unfold ruleValue rule
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one,Arithmetic.one_ne_zero,ite_false,ite_true]
  unfold gen
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major] at *
  simp [Scalar.eval,pack2Value,hp,universalValue]

theorem mpTree_bounds (b p q : V) : p ≤ mpTree b p q ∧ q ≤ mpTree b p q := by
  have ht : pack3Value b p q ≤ mpTree b p q := (pairValue_bounds _ _).2
  have hs : pack2Value p q ≤ pack3Value b p q := (pairValue_bounds _ _).2
  have hp : p ≤ pack2Value p q := (pairValue_bounds _ _).1
  have hq : q ≤ pack2Value p q :=
    le_trans (pairValue_bounds q 0).1 (pairValue_bounds p (pairValue q 0)).2
  exact ⟨le_trans hp (le_trans hs ht),le_trans hq (le_trans hs ht)⟩

theorem genTree_bound (v p : V) : p ≤ genTree v p := by
  exact le_trans (pairValue_bounds p 0).1
    (le_trans (pairValue_bounds v (pairValue p 0)).2 (pairValue_bounds 1 (pack2Value v p)).2)

/-- Common fuel is the sum of both premise fuels, followed by one MP round. -/
noncomputable def mpCertificate (b minor major : V) : V :=
  pairValue (decodeLeft minor + decodeLeft major + 1)
    (mpTree b (decodeRight minor) (decodeRight major))

noncomputable def genCertificate (v child : V) : V :=
  pairValue (decodeLeft child+1) (genTree v (decodeRight child))

section Peano
variable [V↓[ℒₒᵣ] ⊧* theory]

theorem verify_mp (minor major a b : V)
    (hm : verifyValue minor = a+1) (hj : verifyValue major = implicationValue a b+1) :
    verifyValue (mpCertificate b minor major) = b+1 := by
  let t := mpTree b (decodeRight minor) (decodeRight major)
  have hp := (mpTree_bounds b (decodeRight minor) (decodeRight major)).1
  have hq := (mpTree_bounds b (decodeRight minor) (decodeRight major)).2
  have hm' : nth (tableValue (decodeLeft minor+decodeLeft major) t) (decodeRight minor)=a+1 :=
    table_transport _ _ _ _ _ _ le_rfl hp hm
  have hj' : nth (tableValue (decodeLeft minor+decodeLeft major) t) (decodeRight major)=implicationValue a b+1 := by
    simpa only [add_comm] using
      table_transport (decodeLeft major) (decodeLeft minor) (decodeRight major) t
        (decodeRight major) (implicationValue a b) le_rfl hq hj
  simp only [mpCertificate,verifyValue,pair_left,pair_right,table_succ]
  rw [CheckerRows.rows_nth _ _ _ (lt_add_one _)]
  simp only [mpTree,pair_left,pair_right]
  exact mp_rule _ _ _ _ _ hm' hj'

theorem verify_gen (v child a : V) (h : verifyValue child = a+1) :
    verifyValue (genCertificate v child) = universalValue v a+1 := by
  have ht : nth (tableValue (decodeLeft child) (genTree v (decodeRight child)))
      (decodeRight child)=a+1 := by
    rw [table_locality _ _ (decodeRight child) _ (genTree_bound _ _) le_rfl]
    exact h
  simp only [genCertificate,verifyValue,pair_left,pair_right,table_succ]
  rw [CheckerRows.rows_nth _ _ _ (lt_add_one _)]
  simp only [genTree,pair_left,pair_right]
  exact gen_rule _ _ _ _ ht
end Peano

#print axioms mp_rule
#print axioms gen_rule
#print axioms mpTree_bounds
#print axioms genTree_bound
#print axioms verify_mp
#print axioms verify_gen
end PA196.Arithmetic.Certificates
