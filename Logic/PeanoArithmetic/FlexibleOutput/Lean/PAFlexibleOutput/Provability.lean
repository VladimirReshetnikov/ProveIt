import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# Provability of the numeral instances of a formula is recursively enumerable

`provable_substs_re`: for every arithmetical formula `φ(y, c, x)` the relation "`𝗣𝗔` proves
`φ(y, c, x)` at the numerals of `y`, `c`, `x`" is recursively enumerable in `((c, x), y)`.
Nothing is assumed about `φ`.

The route is internal. The triple is read as one number `p`, with Foundation's projections
`π₁`, `π₂`. Foundation's arithmetized provability predicate `Provable 𝗣𝗔` and its formal
substitution of numerals are `𝚺₁`-definable, so the predicate

  `Provable 𝗣𝗔 (subst ?[numeral (π₂ p), numeral (π₁ (π₁ p)), numeral (π₂ (π₁ p))] ⌜φ⌝)`

is `𝚺₁`-definable in `ℕ`, hence recursively enumerable (`re_iff_sigma1`). The code inside is the
Gödel number of the sentence `φ/[y, c, x]`, and the arithmetized provability of a Gödel number
in `ℕ` is real provability (`provable_iff_provable`).

This module does not depend on the other modules of the project.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic
open Bootstrapping Bootstrapping.Arithmetic

/-- The provable numeral instances of an arithmetical formula form a recursively enumerable
relation. -/
theorem provable_substs_re (φ : ArithmeticSemisentence 3) :
    REPred fun p : (ℕ × ℕ) × ℕ => 𝗣𝗔 ⊢ φ/[↑p.2, ↑p.1.1, ↑p.1.2] := by
  have h : 𝚺₁-Predicate fun p : ℕ ↦ Bootstrapping.Provable 𝗣𝗔 (subst ℒₒᵣ
      ?[numeral (π₂ p), numeral (π₁ (π₁ p)), numeral (π₂ (π₁ p))] (⌜φ⌝ : ℕ)) := by definability
  refine ((re_iff_sigma1.mpr h).comp Computable.encode).of_eq fun ⟨⟨c, x⟩, y⟩ => ?_
  -- The projections recover the triple, and the formal substitution computes the Gödel number
  -- of the instance.
  simp [← nat_pair_eq, ← provable_iff_provable (T := 𝗣𝗔), Sentence.quote_def,
    Semiformula.quote_def, Rewriting.emb_subst_eq_subst_emb, Matrix.comp_vecCons',
    Matrix.constant_eq_singleton]

#print axioms provable_substs_re

end PAFlexibleOutput
