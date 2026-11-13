import DiophantineConsistency.ComposeRepresentation
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fin.VecNotation

/-!
# Explicit graph data for natural pairing and inverse projections

The two branches are exactly the quadratic branches of `Nat.pair`.
An inverse projection supplies the missing component as one natural witness.
The data cover every natural input, including zero.
-/

namespace DiophantineConsistency.GraphRep

/-- The two-branch coordinate graph of Mathlib's natural pairing function. -/
def pairCoordinates : GraphRep (fun v : Fin 2 → ℕ => Nat.pair (v 0) (v 1)) := by
  let z : Expr (Option (Fin 2)) := .var none
  let x : Expr (Option (Fin 2)) := .var (some 0)
  let y : Expr (Option (Fin 2)) := .var (some 1)
  let leftEq : Rep (Option (Fin 2)) (fun v => v none = v (some 1) * v (some 1) + v (some 0)) :=
    (Rep.equality z (y * y + x)).ofIff (fun v => by
      simp only [z, x, y, Expr.eval, ← Int.natCast_mul, ← Int.natCast_add, Int.natCast_inj])
  let rightEq : Rep (Option (Fin 2)) (fun v =>
      v none = v (some 0) * v (some 0) + v (some 0) + v (some 1)) :=
    (Rep.equality z (x * x + x + y)).ofIff (fun v => by
      simp only [z, x, y, Expr.eval, ← Int.natCast_mul, ← Int.natCast_add, Int.natCast_inj])
  let left := (ArithmeticRep.lt (some (0 : Fin 2)) (some 1)).conjunction leftEq
  let right := (ArithmeticRep.le (some (1 : Fin 2)) (some 0)).conjunction rightEq
  refine (left.disjunction right).ofIff ?_
  intro v
  change ((v (some 0) < v (some 1) ∧ v none = v (some 1) * v (some 1) + v (some 0)) ∨
    (v (some 1) ≤ v (some 0) ∧ v none = v (some 0) * v (some 0) + v (some 0) + v (some 1))) ↔
    v none = Nat.pair (v (some 0)) (v (some 1))
  by_cases h : v (some 0) < v (some 1)
  · simp [Nat.pair, h, Nat.not_le_of_lt h]
  · simp [Nat.pair, h, Nat.le_of_not_gt h]

/-- Pair explicitly represented functions, retaining both branch certificates. -/
def pair {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) :
    GraphRep (fun v => Nat.pair (f v) (g v)) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact GraphRep.compose pairCoordinates arguments

theorem exists_pair_right_iff (z a : ℕ) :
    (∃ b, z = Nat.pair a b) ↔ a = (Nat.unpair z).1 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair z).2, by rw [h, Nat.pair_unpair]⟩

theorem exists_pair_left_iff (z b : ℕ) :
    (∃ a, z = Nat.pair a b) ↔ b = (Nat.unpair z).2 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair z).1, by rw [h, Nat.pair_unpair]⟩

/-- The first inverse-pairing coordinate graph uses the second as a witness. -/
def unpairLeftCoordinate : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).1) := by
  let index : Option (Fin 2) → Option (Fin 1) ⊕ Fin 1
    | none => .inl (some 0)
    | some i => if i = 0 then .inl none else .inr 0
  refine ((Rep.reindex pairCoordinates index).existsBlock).ofIff ?_
  intro v
  change (∃ w : Fin 1 → ℕ, v (some 0) = Nat.pair (v none) (w 0)) ↔
    v none = (Nat.unpair (v (some 0))).1
  simp [Fin.exists_fin_succ_pi, exists_pair_right_iff]

/-- The second inverse-pairing coordinate graph uses the first as a witness. -/
def unpairRightCoordinate : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).2) := by
  let index : Option (Fin 2) → Option (Fin 1) ⊕ Fin 1
    | none => .inl (some 0)
    | some i => if i = 0 then .inr 0 else .inl none
  refine ((Rep.reindex pairCoordinates index).existsBlock).ofIff ?_
  intro v
  change (∃ w : Fin 1 → ℕ, v (some 0) = Nat.pair (w 0) (v none)) ↔
    v none = (Nat.unpair (v (some 0))).2
  simp [Fin.exists_fin_succ_pi, exists_pair_left_iff]

/-- First inverse-pairing projection of a supplied represented function. -/
def unpairLeft {σ : Type*} {f : (σ → ℕ) → ℕ} (r : GraphRep f) :
    GraphRep (fun v => (Nat.unpair (f v)).1) :=
  GraphRep.compose unpairLeftCoordinate (fun _ => r)

/-- Second inverse-pairing projection of a supplied represented function. -/
def unpairRight {σ : Type*} {f : (σ → ℕ) → ℕ} (r : GraphRep f) :
    GraphRep (fun v => (Nat.unpair (f v)).2) :=
  GraphRep.compose unpairRightCoordinate (fun _ => r)

end DiophantineConsistency.GraphRep
