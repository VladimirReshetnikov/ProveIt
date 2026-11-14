import PA194ComprehensionStep
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194ComprehensionShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma bit_shift :
    (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).shift =
      (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2) := by
  rw [← Semiformula.typed_quote_shift]
  congr 1
  change Rew.shift ▹ (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2) = _
  apply Semiformula.rew_eq_self_of
  · intro x; simp
  · intro x hx
    exfalso
    have he : (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2).freeVariables = ∅ := Semiformula.freeVariables_emb bitDef.val
    change x ∈ (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2).freeVariables at hx
    rw [he] at hx
    simpa using hx
lemma lt_shift :
    (⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).shift =
      (⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2) := by
  rw [Sentence.typed_quote_def]
  rw [← Semiformula.typed_quote_shift]
  congr 1
  change Rew.shift ▹ (Rewriting.emb (“#0 < #1” : ArithmeticSemisentence 2) : ArithmeticSemiformula Nat 2) = _
  apply Semiformula.rew_eq_self_of
  · intro x; simp
  · intro x hx
    exfalso
    have he : (Rewriting.emb (“#0 < #1” : ArithmeticSemisentence 2) : ArithmeticSemiformula Nat 2).freeVariables = ∅ := Semiformula.freeVariables_emb _
    change x ∈ (Rewriting.emb (“#0 < #1” : ArithmeticSemisentence 2) : ArithmeticSemiformula Nat 2).freeVariables at hx
    rw [he] at hx
    simpa using hx
lemma succ_shift :
    (⌜(‘#0 + 1’ : ArithmeticSemiterm Nat 1)⌝ : Bootstrapping.Semiterm V ℒₒᵣ 1).shift =
      (⌜(‘#0 + 1’ : ArithmeticSemiterm Nat 1)⌝ : Bootstrapping.Semiterm V ℒₒᵣ 1) := by
  simp
#print axioms bit_shift
#print axioms lt_shift
#print axioms succ_shift
end PA194ComprehensionShift
