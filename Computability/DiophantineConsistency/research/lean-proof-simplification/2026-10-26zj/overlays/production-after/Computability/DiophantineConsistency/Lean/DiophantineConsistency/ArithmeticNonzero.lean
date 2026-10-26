import DiophantineConsistency.DirectComposition
import Mathlib.Data.Fin.VecNotation

/-!
# One-witness disequality and direct equality branching

An integer is nonzero exactly when its square minus one is a natural
number. This avoids the two independent slacks for the order alternatives.
-/

namespace DiophantineConsistency.Rep

variable {σ : Type*}

/-- A single natural slack represents disequality of any supplied integer
expression, including expressions with negative values. -/
def nonzero (e : Expr σ) : Rep σ (fun v => e.eval (fun i => (v i : ℤ)) ≠ 0) where
  witnessCount := 1
  expression := (e.rename Sum.inl * e.rename Sum.inl - .constant 1) - .var (.inr 0)
  correct v := by
    let z := e.eval (fun i => (v i : ℤ))
    simp only [Expr.eval_sub, Expr.eval_mul, Expr.eval_rename, Expr.eval_constant, Expr.eval_var]
    change z ≠ 0 ↔ ∃ w : Fin 1 → ℕ, z * z - 1 - (w 0 : ℤ) = 0
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le
        (Int.sub_nonneg.mpr (Int.add_one_le_iff.mpr (mul_self_pos.mpr hz)))
      exact ⟨fun _ => n, sub_eq_zero.mpr hn⟩
    · rintro ⟨w, hw⟩
      apply mul_self_pos.mp
      have := Int.natCast_nonneg (w 0)
      omega

end DiophantineConsistency.Rep

namespace DiophantineConsistency.GraphRep

/-- An equality branch with one disequality slack and no hidden classifier. -/
def ifEqDirectCoordinates : GraphRep (fun v : Fin 4 → ℕ =>
    if v 0 = v 1 then v 2 else v 3) := by
  let x : Expr (Option (Fin 4)) := .var (some 0)
  let y : Expr (Option (Fin 4)) := .var (some 1)
  let out : Expr (Option (Fin 4)) := .var none
  let yes := (Rep.equality x y).conjunction (Rep.equality out (.var (some 2)))
  let no := (Rep.nonzero (x - y)).conjunction (Rep.equality out (.var (some 3)))
  refine (yes.disjunction no).ofIff ?_
  intro v
  change (((v (some 0) : ℤ) = (v (some 1) : ℤ) ∧
    (v none : ℤ) = (v (some 2) : ℤ)) ∨
    ((v (some 0) : ℤ) - (v (some 1) : ℤ) ≠ 0 ∧
      (v none : ℤ) = (v (some 3) : ℤ))) ↔ _
  simp only [sub_ne_zero, Int.natCast_inj]
  by_cases h : v (some 0) = v (some 1) <;> simp [h]

theorem ifEqDirectCoordinates_witnessCount : ifEqDirectCoordinates.witnessCount = 1 := rfl

/-- Direct conditional substitution retains the output and uses one branch slack. -/
def ifEqDirect {σ : Type*} {f g h k : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) (t : GraphRep h) (u : GraphRep k) :
    GraphRep (fun v => if f v = g v then h v else k v) := by
  let arguments : ∀ i : Fin 4, GraphRep (![f, g, h, k] i) :=
    Fin.cases r (Fin.cases s (Fin.cases t (Fin.cases u (fun i => Fin.elim0 i))))
  exact composeDirect ifEqDirectCoordinates arguments

end DiophantineConsistency.GraphRep
