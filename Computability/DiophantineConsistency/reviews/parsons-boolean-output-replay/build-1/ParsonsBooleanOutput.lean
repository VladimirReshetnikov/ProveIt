import DiophantineConsistency.ParsonsStructure
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsBooleanOutput
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsStructure ParsonsRule

theorem eval_append (M : Type) [ORingStructure M] (f : ℕ → M)
    (xs ys : List (Proposition ℒₒᵣ)) :
    (disjoin (xs ++ ys)).Evalf f ↔ (disjoin xs).Evalf f ∨ (disjoin ys).Evalf f := by
  induction xs with
  | nil => simp [disjoin]
  | cons P xs ih => simp [disjoin, ih, or_assoc]

noncomputable def collapse_or (xs ys : List (Proposition ℒₒᵣ)) (P Q : Proposition ℒₒᵣ)
    (h : Proof 𝗣𝗔⁻ (disjoin (xs ++ P :: Q :: ys))) :
    Proof 𝗣𝗔⁻ (disjoin (xs ++ (P ⋎ Q) :: ys)) := by
  have hi : Proof 𝗣𝗔⁻ (disjoin (xs ++ P :: Q :: ys) 🡒 disjoin (xs ++ (P ⋎ Q) :: ys)) :=
    ParsonsGuardedCollection.of_semantics _ _ (by
      intro M _ _ f hf
      simpa [eval_append, disjoin, or_assoc] using hf)
  exact .mp hi h

noncomputable def collapse_and (xs ys : List (Proposition ℒₒᵣ)) (P Q : Proposition ℒₒᵣ)
    (hp : Proof 𝗣𝗔⁻ (disjoin (xs ++ P :: ys))) (hq : Proof 𝗣𝗔⁻ (disjoin (xs ++ Q :: ys))) :
    Proof 𝗣𝗔⁻ (disjoin (xs ++ (P ⋏ Q) :: ys)) := by
  have hi : Proof 𝗣𝗔⁻ (disjoin (xs ++ P :: ys) 🡒 (disjoin (xs ++ Q :: ys) 🡒
      disjoin (xs ++ (P ⋏ Q) :: ys))) :=
    ParsonsGuardedCollection.of_semantics _ _ (by
      intro M _ _ f hp
      simp only [LogicalConnective.HomClass.map_imply]
      intro hq
      simp only [eval_append, disjoin, LogicalConnective.HomClass.map_or,
        LogicalConnective.HomClass.map_and] at hp hq ⊢
      change (disjoin xs).Evalf f ∨ (P.Evalf f ∨ (disjoin ys).Evalf f) at hp
      change (disjoin xs).Evalf f ∨ (Q.Evalf f ∨ (disjoin ys).Evalf f) at hq
      change (disjoin xs).Evalf f ∨ ((P.Evalf f ∧ Q.Evalf f) ∨ (disjoin ys).Evalf f)
      tauto)
  exact .mp (.mp hi hp) hq
end DiophantineConsistency.ParsonsBooleanOutput
