module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import PA196.Arithmetic.CompilerLeaves
@[expose] public section
open M6.Arithmetic.PA
namespace PA196.Arithmetic.CompilerSoundness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA M6.PA.SourceCantorInternal HeadGraphs CommandStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def TableRealizes (previous words : V) : Prop := ∀ i a,
  nth previous i=a+1 → Realizes (nth words i) a

theorem nonzero_predecessor (x : V) (h : x≠0) : x=(x-1)+1 := by
  symm
  exact sub_add_self_of_le (one_le_of_zero_lt x (pos_of_ne_zero h))

theorem gen_sound (previous words tag payload out : V) (ih : TableRealizes previous words)
    (h : Scalar.eval CheckerRule.gen previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.gen words tag payload) out := by
  unfold CheckerRule.gen at h
  unfold CompilerRule.gen
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight payload)=0
  · simp only [ht,ite_true] at h ⊢
    by_cases hm : nth previous (decodeLeft (decodeRight payload))=0
    · simp only [hm,ite_true] at h
      exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
    · simp only [hm,ite_false] at h
      rw [gen_expr]
      have he := add_right_cancel h
      rw [← he]
      exact realizes_gen _ _ _ (ih _ _ (nonzero_predecessor _ hm))
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))

theorem mp_sound (previous words tag payload out : V) (ih : TableRealizes previous words)
    (h : Scalar.eval CheckerRule.mp previous tag payload=out+1) :
    Realizes (WordExpression.eval CompilerRule.mp words tag payload) out := by
  unfold CheckerRule.mp at h
  unfold CompilerRule.mp
  simp only [CheckerRule.zero, CheckerRule.one, CheckerRule.accepted, CheckerRule.r1, CheckerRule.r2, CheckerRule.r3, CheckerRule.r4, CheckerRule.a, CheckerRule.b, CheckerRule.c, CheckerRule.u, CheckerRule.h, CheckerRule.requireZero, CheckerRule.minor, CheckerRule.major, CompilerRule.requireZero] at *
  simp only [Scalar.eval,Nat.cast_zero,Nat.cast_one] at h
  simp only [WordExpression.eval,Scalar.eval,Nat.cast_zero]
  by_cases ht : decodeRight (decodeRight (decodeRight payload))=0
  · simp only [ht,ite_true] at h ⊢
    by_cases hm : nth previous (decodeLeft (decodeRight payload))=0
    · simp only [hm,ite_true] at h
      exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
    · simp only [hm,ite_false] at h
      by_cases hj : nth previous (decodeLeft (decodeRight (decodeRight payload)))=0
      · simp only [hj,ite_true] at h
        exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
      · simp only [hj,ite_false] at h
        by_cases he : nth previous (decodeLeft (decodeRight (decodeRight payload)))=
          ActualArithmeticGraph.eval implicationExpr (nth previous (decodeLeft (decodeRight payload))-1)
            (decodeLeft payload) 0 0 +1
        · simp only [he,ite_true] at h
          have ho := add_right_cancel h
          rw [← ho]
          simp only [LiteralWords.literal_expr,mp_expr]
          exact realizes_mp _ _ _ _ (ih _ _ he) (ih _ _ (nonzero_predecessor _ hm))
        · simp only [he,ite_false] at h
          exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
  · simp only [ht,ite_false] at h
    exact False.elim ((ne_of_lt (lt_add_one out)).elim (by simpa using h.symm))
#print axioms mp_sound
#print axioms gen_sound
end PA196.Arithmetic.CompilerSoundness

