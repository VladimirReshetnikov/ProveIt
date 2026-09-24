import Mathlib.NumberTheory.Dioph
import Mathlib.Data.Nat.Pairing

/-!
# Diophantine pairing and unpairing

Mathlib's natural pairing function has two polynomial branches. Its inverse
projections can therefore be represented by existentially supplying the
other component, using the pairing identities. The formulas apply to all
natural inputs, including zero, and require no finite input index type.
-/

namespace Diophantine

open Dioph

/-- Pairing preserves Diophantine functions. The two branches are exactly
the branches in Mathlib's `Nat.pair`. -/
theorem pair_dioph {α : Type} {f g : (α → ℕ) → ℕ}
    (hf : DiophFn f) (hg : DiophFn g) :
    DiophFn (fun v => Nat.pair (f v) (g v)) := by
  change Dioph {v : Option α → ℕ |
    Nat.pair (f (v ∘ some)) (g (v ∘ some)) = v none}
  have hf' := Dioph.reindex_diophFn some hf
  have hg' := Dioph.reindex_diophFn some hg
  have hleft := Dioph.eq_dioph
    (Dioph.add_dioph (Dioph.mul_dioph hg' hg') hf') (Dioph.proj_dioph none)
  have hright := Dioph.eq_dioph
    (Dioph.add_dioph (Dioph.add_dioph (Dioph.mul_dioph hf' hf') hf') hg')
    (Dioph.proj_dioph none)
  refine Dioph.ext
    (((Dioph.lt_dioph hf' hg').inter hleft).union
      ((Dioph.le_dioph hg' hf').inter hright)) ?_
  intro v
  change ((f (v ∘ some) < g (v ∘ some) ∧
      g (v ∘ some) * g (v ∘ some) + f (v ∘ some) = v none) ∨
    (g (v ∘ some) ≤ f (v ∘ some) ∧
      f (v ∘ some) * f (v ∘ some) + f (v ∘ some) + g (v ∘ some) = v none)) ↔
    Nat.pair (f (v ∘ some)) (g (v ∘ some)) = v none
  by_cases hlt : f (v ∘ some) < g (v ∘ some)
  · simp [Nat.pair, hlt, Nat.not_le_of_lt hlt]
  · simp [Nat.pair, hlt, Nat.le_of_not_gt hlt]

/-- The first inverse-pairing projection preserves Diophantine functions.
An existential natural witness supplies the second component. -/
theorem unpair_left_dioph {α : Type} {f : (α → ℕ) → ℕ}
    (hf : DiophFn f) : DiophFn (fun v => (Nat.unpair (f v)).1) := by
  change Dioph {v : Option α → ℕ | (Nat.unpair (f (v ∘ some))).1 = v none}
  have hgraph : Dioph {v : Option (Option α) → ℕ |
      Nat.pair (v (some none)) (v none) = f (fun idx => v (some (some idx)))} :=
    Dioph.eq_dioph
      (pair_dioph (Dioph.proj_dioph (some none)) (Dioph.proj_dioph none))
      (Dioph.reindex_diophFn (fun idx => some (some idx)) hf)
  have hex : Dioph {v : Option α → ℕ |
      ∃ other : ℕ, Nat.pair (v none) other = f (v ∘ some)} :=
    Dioph.ex1_dioph hgraph
  refine Dioph.ext hex ?_
  intro v
  change (∃ other : ℕ, Nat.pair (v none) other = f (v ∘ some)) ↔
    (Nat.unpair (f (v ∘ some))).1 = v none
  constructor
  · rintro ⟨other, heq⟩
    simp only [← heq, Nat.unpair_pair]
  · intro heq
    refine ⟨(Nat.unpair (f (v ∘ some))).2, ?_⟩
    rw [← heq, Nat.pair_unpair]

/-- The second inverse-pairing projection preserves Diophantine functions.
An existential natural witness supplies the first component. -/
theorem unpair_right_dioph {α : Type} {f : (α → ℕ) → ℕ}
    (hf : DiophFn f) : DiophFn (fun v => (Nat.unpair (f v)).2) := by
  change Dioph {v : Option α → ℕ | (Nat.unpair (f (v ∘ some))).2 = v none}
  have hgraph : Dioph {v : Option (Option α) → ℕ |
      Nat.pair (v none) (v (some none)) = f (fun idx => v (some (some idx)))} :=
    Dioph.eq_dioph
      (pair_dioph (Dioph.proj_dioph none) (Dioph.proj_dioph (some none)))
      (Dioph.reindex_diophFn (fun idx => some (some idx)) hf)
  have hex : Dioph {v : Option α → ℕ |
      ∃ other : ℕ, Nat.pair other (v none) = f (v ∘ some)} :=
    Dioph.ex1_dioph hgraph
  refine Dioph.ext hex ?_
  intro v
  change (∃ other : ℕ, Nat.pair other (v none) = f (v ∘ some)) ↔
    (Nat.unpair (f (v ∘ some))).2 = v none
  constructor
  · rintro ⟨other, heq⟩
    simp only [← heq, Nat.unpair_pair]
  · intro heq
    refine ⟨(Nat.unpair (f (v ∘ some))).1, ?_⟩
    rw [← heq, Nat.pair_unpair]

end Diophantine
