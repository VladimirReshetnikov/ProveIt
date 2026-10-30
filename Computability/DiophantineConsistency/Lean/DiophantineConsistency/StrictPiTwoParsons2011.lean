import DiophantineConsistency.StrictPiTwoCurrent2011
import DiophantineConsistency.ParsonsStrictInitial

/-!
# From `𝗜𝚺₁` to the Parsons rule calculus, for strict Π₂ conclusions

`StrictSigmaOneInduction.StrictSigma` is definitionally
`ParsonsStrictInvariant.Strict`, so an `𝗜𝚺₁` theorem has a proof from `𝗣𝗔⁻` and
strict `Σ₁` induction (`isigma1_provable`), which `ParsonsStrictInitial.strict_fragment`
translates into the explicit rule calculus whenever the conclusion is
`Tree`-described. A universally closed strict existential prefix over a `Σ₀`
matrix is `Tree`-described (`sentence_tree_itr`), so:

* `rule_proof_of_isigma1`: every `𝗜𝚺₁` theorem `∀⁰* (∃⁰^[k] D)` with `D` `Σ₀` has a
  `ParsonsRule.Proof 𝗣𝗔⁻`;
* `nf_rule_proof`: in particular the strict normal form of the current
  equivalence, given the `𝗜𝚺₁` endpoint.
-/
set_option autoImplicit false

namespace DiophantineConsistency.StrictPiTwoParsons2011

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction StrictPiTwoCurrent2011 ParsonsGuardTree ParsonsRule

theorem strict_eq : StrictSigma = ParsonsStrictInvariant.Strict := rfl

theorem sentence_tree_itr {n k : ℕ} (D : Semisentence ℒₒᵣ (n + k)) (hD : Hierarchy 𝚺 0 D) :
    Tree (Rewriting.emb (∀⁰* (∃⁰^[k] D)) : Proposition ℒₒᵣ) := by
  have h : Hierarchy 𝚺 1 (∃⁰^[k] (Rew.emb ▹ D) : ArithmeticSemiformula ℕ n) :=
    Hierarchy.exsItr_iff.mpr ((Hierarchy.rew _ hD).mono (by decide))
  have ht := ParsonsStrictPrefixTree.of_guard (ParsonsGuardClosure.closure _ h)
  simpa [Rewriting.emb] using ht

/-- **Every strict Π₂ theorem of `𝗜𝚺₁` has a Parsons rule proof.** -/
theorem rule_proof_of_isigma1 {n k : ℕ} (D : Semisentence ℒₒᵣ (n + k)) (hD : Hierarchy 𝚺 0 D)
    (h : 𝗜𝚺₁ ⊢ ∀⁰* (∃⁰^[k] D)) : Nonempty (Proof 𝗣𝗔⁻ (Rewriting.emb (∀⁰* (∃⁰^[k] D)))) := by
  obtain ⟨p⟩ := isigma1_provable h
  exact ParsonsStrictInitial.strict_fragment
    (p : Theory.Proof (𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ ParsonsStrictInvariant.Strict) _)
    (sentence_tree_itr D hD)

/-- **The current strict normal form has a Parsons rule proof**, given the endpoint. -/
theorem nf_rule_proof
    (h : 𝗜𝚺₁ ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘 conSentence) :
    Nonempty (Proof 𝗣𝗔⁻ (Rewriting.emb nf)) := by
  obtain ⟨D, hD, hnf⟩ := nf_shape
  have hp := isigma1_nf h
  rw [hnf] at hp ⊢
  exact rule_proof_of_isigma1 D hD hp

end DiophantineConsistency.StrictPiTwoParsons2011
