import PA194SemanticCollision

/-! Scope of the native-decoder collision and the irreflexivity needed to rule
out this particular counterexample. This is standard named-formula semantics. -/
namespace PA194SemanticCollision
open M6.PA.NativeCalculus

theorem decoded_translation_false_any {V : Type} (R E : V → V → Prop)
    (env : Nat → V) (z : Nat) :
    ¬ (NumericDecode.decode (PA194Logic.Relational.relationalCode z source)).eval R E env := by
  rw [numeric_collision,NumericDecode.decode_neg,NumericDecode.decode_zero]
  simp [Named.eval]

theorem source_false_irreflexive {V : Type} (R E : V → V → Prop)
    (env : Nat → V) (hirr : ∀ x, ¬ R x x) : ¬ source.eval R E env := by
  simp only [source,Named.eval]
  intro h
  exact hirr (env 0) (h trivial)

theorem collision_example_agrees_irreflexive {V : Type} (R E : V → V → Prop)
    (env : Nat → V) (z : Nat) (hirr : ∀ x, ¬ R x x) :
    (NumericDecode.decode (PA194Logic.Relational.relationalCode z source)).eval R E env ↔
      source.eval R E env := by
  constructor
  · intro ht; exact False.elim (decoded_translation_false_any R E env z ht)
  · intro hs; exact False.elim (source_false_irreflexive R E env hirr hs)

#print axioms decoded_translation_false_any
#print axioms source_false_irreflexive
#print axioms collision_example_agrees_irreflexive
end PA194SemanticCollision
