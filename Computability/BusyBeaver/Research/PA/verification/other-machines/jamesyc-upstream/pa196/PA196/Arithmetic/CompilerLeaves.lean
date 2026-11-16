module
public import PA196.Arithmetic.RealizesFormula
public import PA196.Arithmetic.CheckerRule
public import PA196.Arithmetic.CompilerRule
@[expose] public section
namespace PA196.Arithmetic.CompilerSoundness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA M6.PA.SourceCantorInternal HeadGraphs CommandStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem leaf1_sound (previous words tag payload out : V)
    (h : Scalar.eval CheckerRule.leaf1 previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.leaf1 words tag payload) out := by
  unfold CheckerRule.leaf1 at h
  unfold CompilerRule.leaf1
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight payload)=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval head1Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) 0 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head1 _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf2_sound (previous words tag payload out : V)
    (h : Scalar.eval CheckerRule.leaf2 previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.leaf2 words tag payload) out := by
  unfold CheckerRule.leaf2 at h
  unfold CompilerRule.leaf2
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval head2Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) (decodeLeft (decodeRight (decodeRight payload))) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head2 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf3_sound (previous words tag payload out : V)
    (h : Scalar.eval CheckerRule.leaf3 previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.leaf3 words tag payload) out := by
  unfold CheckerRule.leaf3 at h
  unfold CompilerRule.leaf3
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval head3Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) (decodeLeft (decodeRight (decodeRight payload))) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head3 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf4_sound (previous words tag payload out : V)
    (h : Scalar.eval CheckerRule.leaf4 previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.leaf4 words tag payload) out := by
  unfold CheckerRule.leaf4 at h
  unfold CompilerRule.leaf4
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval head4Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) (decodeLeft (decodeRight (decodeRight payload))) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head4 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf5_sound (previous words tag payload out : V)
    (h : Scalar.eval CheckerRule.leaf5 previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.leaf5 words tag payload) out := by
  unfold CheckerRule.leaf5 at h
  unfold CompilerRule.leaf5
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight payload)=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval head5Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) 0 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head5 _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf6_sound (previous words tag payload out : V)
    (h : Scalar.eval CheckerRule.leaf6 previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.leaf6 words tag payload) out := by
  unfold CheckerRule.leaf6 at h
  unfold CompilerRule.leaf6
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    rw [selectedHead_expr]
    have he : ActualArithmeticGraph.eval head6Expr (decodeLeft payload)
      (decodeLeft (decodeRight payload)) (decodeLeft (decodeRight (decodeRight payload))) 0=out := add_right_cancel h
    rw [← he]
    exact realizes_head6 _ _ _
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
theorem leaf8_sound (previous words tag payload out : V)
    (h : Scalar.eval CheckerRule.leaf8 previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.leaf8 words tag payload) out := by
  unfold CheckerRule.leaf8 at h
  unfold CompilerRule.leaf8
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight (decodeRight payload)))=0
  · simp only [ht,ite_true] at h ⊢
    by_cases hu : decodeLeft (decodeRight (decodeRight (decodeRight payload))) ≤ decodeLeft payload
    · simp only [hu,ite_true] at h ⊢
      rw [rho8_expr]
      have he := add_right_cancel h
      rw [← he]
      exact realizes_rho8 _ _ _ _ hu
    · simp only [hu,ite_false] at h
      exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))

theorem bundle_sound (previous words tag payload out : V)
    (h : Scalar.eval CheckerRule.rawBundle previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.rawBundle words tag payload) out := by
  unfold CheckerRule.rawBundle at h
  unfold CompilerRule.rawBundle
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    by_cases ha : decodeLeft (decodeRight (decodeRight payload))=decodeLeft payload
    · simp only [ha,ite_true] at h
      exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
    · simp only [ha,ite_false] at h ⊢
      by_cases hb : decodeLeft (decodeRight (decodeRight payload))=decodeLeft (decodeRight payload)
      · simp only [hb,ite_true] at h
        exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
      · simp only [hb,ite_false] at h ⊢
        rw [gate_expr]
        have he := add_right_cancel h
        rw [← he]
        have hg := realizes_gate (decodeLeft payload) (decodeLeft (decodeRight payload))
          (decodeLeft (decodeRight (decodeRight payload)))
        have hz : decodeLeft (0:V)=0 := by simp [decodeLeft]
        simpa only [gateValue,ha,hb,ite_false,Scalar.eval,hz] using hg
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
#print axioms leaf1_sound
#print axioms leaf6_sound
#print axioms leaf8_sound
#print axioms bundle_sound
end PA196.Arithmetic.CompilerSoundness
