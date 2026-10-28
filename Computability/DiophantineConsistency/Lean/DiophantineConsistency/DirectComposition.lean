import DiophantineConsistency.ComposeRepresentation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Graph substitution without copying the output coordinate

The substituted input values need witnesses; the already exposed graph
output does not. This constructor retains that output directly.
-/

namespace DiophantineConsistency.Rep

open scoped BigOperators

theorem allFin_witnessCount {σ : Type*} (n : ℕ) :
    ∀ (P : Fin n → (σ → ℕ) → Prop) (rs : ∀ i, Rep σ (P i)),
      (allFin n P rs).witnessCount = ∑ i, (rs i).witnessCount := by
  induction n with
  | zero => intro P rs; rfl
  | succ n ih =>
      intro P rs
      change (rs 0).witnessCount +
        (allFin n (fun i => P i.succ) (fun i => rs i.succ)).witnessCount = _
      rw [ih, Fin.sum_univ_succ]

end DiophantineConsistency.Rep

namespace DiophantineConsistency.GraphRep

open scoped BigOperators

variable {σ : Type*} {n : ℕ} {f : (Fin n → ℕ) → ℕ}
  {g : Fin n → (σ → ℕ) → ℕ}

/-- Substitute the supplied graph inputs while retaining the original output
coordinate. Exactly the `n` input values become new existential witnesses. -/
def composeDirect (r : GraphRep f) (s : ∀ i, GraphRep (g i)) :
    GraphRep (fun v => f (fun i => g i v)) := by
  let index : Option (Fin n) → Option σ ⊕ Fin n
    | none => .inl none
    | some i => .inr i
  let slot (i : Fin n) : Option σ → Option σ ⊕ Fin n
    | none => .inr i
    | some j => .inl (some j)
  let rows := Rep.allFin n
    (fun i (v : Option σ ⊕ Fin n → ℕ) => v (.inr i) = g i (fun j => v (.inl (some j))))
    (fun i => Rep.reindex (s i) (slot i))
  refine (((Rep.reindex r index).conjunction rows).existsBlock).ofIff ?_
  intro v
  change (∃ a : Fin n → ℕ, v none = f a ∧
    ∀ i, a i = g i (v ∘ some)) ↔ v none = f (fun i => g i (v ∘ some))
  simp only [← funext_iff, exists_eq_right]

theorem composeDirect_witnessCount (r : GraphRep f) (s : ∀ i, GraphRep (g i)) :
    (composeDirect r s).witnessCount = n + (r.witnessCount + ∑ i, (s i).witnessCount) := by
  simp only [composeDirect, Rep.ofIff, Rep.existsBlock, Rep.conjunction, Rep.reindex,
    Rep.allFin_witnessCount]

theorem compose_witnessCount (r : GraphRep f) (s : ∀ i, GraphRep (g i)) :
    (GraphRep.compose r s).witnessCount = (n + 1) + (r.witnessCount + ∑ i, (s i).witnessCount) := by
  simp only [GraphRep.compose, Rep.compose, Rep.ofIff, Rep.existsBlock, Rep.conjunction,
    Rep.reindex, Rep.allFin_witnessCount, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    GraphRep.coordinate, GraphRep.reindex, Rep.equality, Nat.zero_add]

/-- Retaining the exposed output saves exactly one existential witness on
every finite graph composition, including zero-input functions. -/
theorem composeDirect_saves_one (r : GraphRep f) (s : ∀ i, GraphRep (g i)) :
    (composeDirect r s).witnessCount + 1 = (GraphRep.compose r s).witnessCount := by
  rw [composeDirect_witnessCount, compose_witnessCount]
  omega

end DiophantineConsistency.GraphRep
