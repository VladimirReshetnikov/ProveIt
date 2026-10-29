import DiophantineConsistency.ParsonsStrictInitial
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsStrictPiTwo
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsGuardTree ParsonsStrictInvariant ParsonsRule

theorem tree {n : ℕ} (D : ArithmeticSemiformula ℕ (n+1)) (hD : Hierarchy 𝚺 0 D) :
    Tree (∀⁰* (∃⁰ D)) := by
  have h : Hierarchy 𝚺 1 (∃⁰ D) := Hierarchy.exs (hD.mono (by decide))
  exact ParsonsStrictPrefixTree.of_guard (ParsonsGuardClosure.closure (∃⁰ D) h)

theorem sentence_tree {n : ℕ} (D : Semisentence ℒₒᵣ (n+1)) (hD : Hierarchy 𝚺 0 D) :
    Tree (Rewriting.emb (∀⁰* (∃⁰ D)) : Proposition ℒₒᵣ) := by
  have h := tree (Rew.emb ▹ D) (Hierarchy.rew Rew.emb hD)
  simpa [Rewriting.emb] using h

theorem strict_fragment {n : ℕ} (D : Semisentence ℒₒᵣ (n+1)) (hD : Hierarchy 𝚺 0 D)
    (p : Theory.Proof (𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ Strict) (∀⁰* (∃⁰ D))) :
    Nonempty (Proof 𝗣𝗔⁻ (Rewriting.emb (∀⁰* (∃⁰ D)))) :=
  ParsonsStrictInitial.strict_fragment p (sentence_tree D hD)
end DiophantineConsistency.ParsonsStrictPiTwo
