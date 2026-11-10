import PAFlexibleOutput.Halting
import Foundation.FirstOrder.Incompleteness.First
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-!
# The refuted outputs form a recursively enumerable relation

`refutationsRE`: the relation "`𝗣𝗔` proves that program `c` does not halt on input `x` with
output `y`" is recursively enumerable in `((c, x), y)`.

The route is internal. Foundation's arithmetized provability predicate `Provable 𝗣𝗔` and its
formal substitution of numerals are `𝚺₁`-definable, so the relation

  `Provable 𝗣𝗔 (neg (subst ?[numeral y, numeral c, numeral x] ⌜universalGraph⌝))`

is `𝚺₁`-definable in `ℕ` (`refutation_sigma1`), hence recursively enumerable
(`rePred_of_sigma1`). The code inside is the Gödel number of the sentence
`∼(haltSentence c x y)` (`neg_subst_quote`), and the arithmetized provability of a Gödel number
in `ℕ` is real provability (`provable_iff_provable`).
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic
open Bootstrapping Bootstrapping.Arithmetic

/-- A ternary relation on `ℕ` that is `𝚺₁`-definable is recursively enumerable. The unary
case is Foundation's `re_iff_sigma1`. -/
lemma rePred_of_sigma1 {P : ℕ → ℕ → ℕ → Prop} (h : 𝚺₁-Relation₃ P) :
    REPred fun p : ℕ × ℕ × ℕ => P p.1 p.2.1 p.2.2 := by
  rcases h with ⟨φ, hφ⟩
  have : REPred fun p : ℕ × ℕ × ℕ ↦
      (Semiformula.Eval (p.1 ::ᵥ p.2.1 ::ᵥ p.2.2 ::ᵥ List.Vector.nil).get id) φ.val :=
    (sigma1_re id (φ.sigma_prop)).comp
      (Primrec.to_comp <| Primrec.vector_cons.comp .fst <|
        Primrec.vector_cons.comp (.comp .fst .snd) <|
        Primrec.vector_cons.comp (.comp .snd .snd) <| .const _)
  exact this.of_eq <| by
    rintro ⟨a, b, c⟩
    simpa [List.Vector.cons_get, Matrix.empty_eq] using hφ ![a, b, c]

/-- Internal refutability of an output is a `𝚺₁` relation of program code, input and output. -/
lemma refutation_sigma1 : 𝚺₁-Relation₃ fun c x y : ℕ ↦
    Bootstrapping.Provable 𝗣𝗔 (neg ℒₒᵣ <| subst ℒₒᵣ
      ?[numeral y, numeral c, numeral x] (⌜universalGraph⌝ : ℕ)) := by
  definability

/-- The code of the negated halting sentence, computed by formal substitution of numerals. -/
lemma neg_subst_quote (c x y : ℕ) :
    neg ℒₒᵣ (subst ℒₒᵣ ?[numeral y, numeral c, numeral x] (⌜universalGraph⌝ : ℕ))
      = ⌜(∼(universalGraph/[↑y, ↑c, ↑x]) : ArithmeticSentence)⌝ := by
  have h := substNumerals_app_quote (V := ℕ) universalGraph ![y, c, x]
  have hfun : (fun i : Fin 3 ↦ ((![y, c, x] i : ℕ) : Semiterm ℒₒᵣ Empty 0))
      = ![(↑y : Semiterm ℒₒᵣ Empty 0), ↑c, ↑x] :=
    funext fun | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => rfl
  -- At `V := ℕ` the model cast `ℕ → V` is the identity, but only propositionally.
  simp only [hfun, natCast_nat] at h
  rw [show subst ℒₒᵣ ?[numeral y, numeral c, numeral x] (⌜universalGraph⌝ : ℕ)
    = ⌜(universalGraph/[↑y, ↑c, ↑x] : ArithmeticSentence)⌝ from h]
  simp [Sentence.quote_def, Semiformula.quote_def]

/-- The refuted outputs form a recursively enumerable relation of program, input and output. -/
theorem refutationsRE :
    REPred fun p : (Code × ℕ) × ℕ => 𝗣𝗔 ⊢ ∼haltSentence p.1.1 p.1.2 p.2 := by
  have hc : Computable fun p : (Code × ℕ) × ℕ => (Encodable.encode p.1.1, p.1.2, p.2) :=
    (Computable.encode.comp (Computable.fst.comp Computable.fst)).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd)
  exact ((rePred_of_sigma1 refutation_sigma1).comp hc).of_eq fun p => by
    show Bootstrapping.Provable 𝗣𝗔 _ ↔ _
    rw [neg_subst_quote]
    exact provable_iff_provable

#print axioms refutationsRE

end PAFlexibleOutput
