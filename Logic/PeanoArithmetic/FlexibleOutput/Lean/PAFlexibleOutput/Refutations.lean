import PAFlexibleOutput.Statement
import Foundation.FirstOrder.Incompleteness.First

/-!
# The refuted outputs form a recursively enumerable relation

`refutationsRE : RefutationsRE` says that the relation "`𝗣𝗔` proves that program `c` does not
halt on input `0` with output `y`" is recursively enumerable in `(c, y)`.

The route is internal. Foundation's arithmetized provability predicate `Provable 𝗣𝗔` and its
formal substitution of numerals are `𝚺₁`-definable, so the relation

  `Provable 𝗣𝗔 (neg (subst ?[numeral y, numeral c, numeral x] ⌜universalGraph⌝))`

is `𝚺₁`-definable in `ℕ` (`refutation_sigma1`), hence recursively enumerable
(`rePred_of_sigma1_rel`). The code inside is the Gödel number of the sentence
`∼(haltSentence c x y)` (`neg_subst_quote`), and the arithmetized provability of a Gödel number
in `ℕ` is real provability (`provable_iff_provable`).
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic
open Bootstrapping Bootstrapping.Arithmetic

/-- A binary relation on `ℕ` that is `𝚺₁`-definable (with parameters) is recursively
enumerable. The unary case is Foundation's `re_iff_sigma1`. -/
lemma rePred_of_sigma1_rel {P : ℕ → ℕ → Prop} (h : 𝚺₁-Relation P) :
    REPred fun p : ℕ × ℕ => P p.1 p.2 := by
  rcases h with ⟨φ, hφ⟩
  have : REPred fun p : ℕ × ℕ ↦
      (Semiformula.Eval (p.1 ::ᵥ p.2 ::ᵥ List.Vector.nil).get id) φ.val :=
    (sigma1_re id (φ.sigma_prop)).comp
      (Primrec.to_comp <| Primrec.vector_cons.comp .fst <|
        Primrec.vector_cons.comp .snd <| .const _)
  exact this.of_eq <| by
    rintro ⟨a, b⟩
    simpa [List.Vector.cons_get, Matrix.empty_eq] using hφ ![a, b]

/-- Internal refutability of an output is a `𝚺₁` relation of the program code and the
output. -/
lemma refutation_sigma1 (x : ℕ) : 𝚺₁-Relation fun c y : ℕ ↦
    Bootstrapping.Provable 𝗣𝗔 (neg ℒₒᵣ <| subst ℒₒᵣ
      ?[numeral y, numeral c, numeral x] (⌜universalGraph⌝ : ℕ)) := by
  definability

/-- The formal substitution of three numerals into the code of the halting formula is the code
of the substituted sentence. -/
lemma subst_quote (c y x : ℕ) :
    subst ℒₒᵣ ?[numeral y, numeral c, numeral x] (⌜universalGraph⌝ : ℕ)
      = ⌜(universalGraph/[↑y, ↑c, ↑x] : ArithmeticSentence)⌝ := by
  have h := substNumerals_app_quote (V := ℕ) universalGraph ![y, c, x]
  have hfun : (fun i : Fin 3 ↦ ((![y, c, x] i : ℕ) : Semiterm ℒₒᵣ Empty 0))
      = ![(↑y : Semiterm ℒₒᵣ Empty 0), ↑c, ↑x] := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  rw [hfun] at h
  -- At `V := ℕ` the model cast `ℕ → V` is the identity, but only propositionally.
  simp only [natCast_nat] at h
  exact h

/-- The code of the negated halting sentence. -/
lemma neg_subst_quote (c y x : ℕ) :
    neg ℒₒᵣ (subst ℒₒᵣ ?[numeral y, numeral c, numeral x] (⌜universalGraph⌝ : ℕ))
      = ⌜(∼(universalGraph/[↑y, ↑c, ↑x]) : ArithmeticSentence)⌝ := by
  rw [subst_quote]
  simp [Sentence.quote_def, Semiformula.quote_def]

/-- Internal refutability in `ℕ` is refutability in `𝗣𝗔`. -/
lemma provable_neg_iff (c : Code) (x y : ℕ) :
    Bootstrapping.Provable 𝗣𝗔 (neg ℒₒᵣ <| subst ℒₒᵣ
        ?[numeral y, numeral (Encodable.encode c), numeral x] (⌜universalGraph⌝ : ℕ))
      ↔ 𝗣𝗔 ⊢ ∼(haltSentence c x y) := by
  rw [neg_subst_quote]
  exact provable_iff_provable

/-- The refuted outputs of the programs on input `0` form a recursively enumerable relation. -/
theorem refutationsRE : RefutationsRE := by
  have h := rePred_of_sigma1_rel (refutation_sigma1 0)
  have hc : Computable fun p : Code × ℕ => (Encodable.encode p.1, p.2) :=
    (Computable.encode.comp Computable.fst).pair Computable.snd
  exact (h.comp hc).of_eq fun p => provable_neg_iff p.1 0 p.2

#print axioms refutationsRE

end PAFlexibleOutput
