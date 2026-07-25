/-!
# Generic counterexample lemmas

A quantifier-swap counterexample always ends the same way: one nesting order
holds, the other fails, so the swap implication and the equivalence both
fail.  These two facts are pure propositional logic, shared by the `∄` and
`∃!` countermodels (Rocq/Coq twin: `implication_fails` / `not_equivalent`
in `Counterexamples.v`).
-/

namespace LeanProofs
namespace QuantifierCommutation

/-- If `A` holds and `B` fails, the implication `A → B` fails. -/
theorem implication_fails {A B : Prop} (ha : A) (hnb : ¬B) : ¬(A → B) :=
  fun h => hnb (h ha)

/-- If `A` holds and `B` fails, the equivalence `A ↔ B` fails. -/
theorem not_equivalent {A B : Prop} (ha : A) (hnb : ¬B) : ¬(A ↔ B) :=
  fun h => hnb (h.mp ha)

end QuantifierCommutation
end LeanProofs
