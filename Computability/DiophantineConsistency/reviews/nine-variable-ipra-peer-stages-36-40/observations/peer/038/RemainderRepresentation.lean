import DiophantineConsistency.DivisionRepresentation
import Mathlib.Tactic.Push

/-!
# Explicit graph data for natural division and remainder

Zero divisors are included: natural division by zero returns zero, and
remainder modulo zero returns the dividend.
-/

namespace DiophantineConsistency.GraphRep

private def compareTwo {σ : Type*} {P : (Fin 2 → ℕ) → Prop}
    {f g : (σ → ℕ) → ℕ} (r : Rep (Fin 2) P) (s : GraphRep f) (t : GraphRep g) :
    Rep σ (fun v => P (fun i => ![f, g] i v)) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases s (Fin.cases t (fun i => Fin.elim0 i))
  exact Rep.compose r arguments

private def zeroAt {σ : Type*} (i : σ) : Rep σ (fun v => v i = 0) :=
  (Rep.equality (Expr.var i) 0).ofIff (fun v => by simp [Expr.eval])

private theorem remainder_criterion (z x y : ℕ) :
    ((y = 0 ∨ z < y) ∧ ∃ q : ℕ, z + y * q = x) ↔ z = x % y := by
  constructor
  · rintro ⟨hy, q, hq⟩
    have he : x % y = z := by
      rw [← hq, Nat.add_mul_mod_self_left]
      rcases hy with h | h
      · simp [h]
      · exact Nat.mod_eq_of_lt h
    exact he.symm
  · intro hz
    subst z
    refine ⟨?_, x / y, Nat.mod_add_div x y⟩
    by_cases hy : y = 0
    · exact Or.inl hy
    · exact Or.inr (Nat.mod_lt _ (Nat.pos_of_ne_zero hy))

private theorem division_criterion (z x y : ℕ) :
    (y = 0 ∧ z = 0 ∨ z * y ≤ x ∧ x < (z + 1) * y) ↔ z = x / y := by
  rcases Nat.eq_zero_or_pos y with hy | hy
  · simp [hy]
  · simp only [Nat.ne_of_gt hy, false_and, false_or]
    rw [eq_comm, Nat.div_eq_iff hy, Nat.add_mul, Nat.one_mul]
    omega

/-- The coordinate remainder graph, with a quotient witness and a strict-bound slack. -/
def modCoordinates : GraphRep (fun v : Fin 2 → ℕ => v 0 % v 1) := by
  let limits := (zeroAt (some (1 : Fin 2))).disjunction
    (ArithmeticRep.lt (none : Option (Fin 2)) (some 1))
  let eqn : Rep (Option (Fin 2) ⊕ Fin 1) (fun v =>
      v (.inl none) + v (.inl (some 1)) * v (.inr 0) = v (.inl (some 0))) :=
    (Rep.equality
      (Expr.var (.inl none) + Expr.var (.inl (some (1 : Fin 2))) * Expr.var (.inr (0 : Fin 1)))
      (Expr.var (.inl (some (0 : Fin 2))))).ofIff (fun v => by
        simp only [Expr.eval, ← Int.natCast_mul, ← Int.natCast_add, Int.natCast_inj])
  refine (limits.conjunction eqn.existsBlock).ofIff ?_
  intro v
  change ((v (some 1) = 0 ∨ v none < v (some 1)) ∧
    ∃ q : Fin 1 → ℕ, v none + v (some 1) * q 0 = v (some 0)) ↔
      v none = v (some 0) % v (some 1)
  have he : (∃ q : Fin 1 → ℕ, v none + v (some 1) * q 0 = v (some 0)) ↔
      ∃ q : ℕ, v none + v (some 1) * q = v (some 0) := by
    constructor
    · rintro ⟨q, hq⟩; exact ⟨q 0, hq⟩
    · rintro ⟨q, hq⟩; exact ⟨fun _ => q, hq⟩
  rw [he]
  exact remainder_criterion _ _ _

/-- The coordinate quotient graph, including the zero-divisor branch. -/
def divCoordinates : GraphRep (fun v : Fin 2 → ℕ => v 0 / v 1) := by
  let out : GraphRep (fun v : Option (Fin 2) → ℕ => v none) := GraphRep.coordinate none
  let x : GraphRep (fun v : Option (Fin 2) → ℕ => v (some 0)) := GraphRep.coordinate (some 0)
  let y : GraphRep (fun v : Option (Fin 2) → ℕ => v (some 1)) := GraphRep.coordinate (some 1)
  let lower := compareTwo (ArithmeticRep.le (0 : Fin 2) 1) (out.mul y) x
  let upper := compareTwo (ArithmeticRep.lt (0 : Fin 2) 1) x
    ((out.add (GraphRep.constant 1)).mul y)
  let zeroCase := (zeroAt (some (1 : Fin 2))).conjunction (zeroAt (none : Option (Fin 2)))
  refine (zeroCase.disjunction (lower.conjunction upper)).ofIff ?_
  intro v
  exact division_criterion _ _ _

/-- Remainder of explicitly represented functions, with no choice of polynomial data. -/
def mod {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) : GraphRep (fun v => f v % g v) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact GraphRep.compose modCoordinates arguments

/-- Quotient of explicitly represented functions, with its zero-divisor convention. -/
def div {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) : GraphRep (fun v => f v / g v) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact GraphRep.compose divCoordinates arguments

end DiophantineConsistency.GraphRep
