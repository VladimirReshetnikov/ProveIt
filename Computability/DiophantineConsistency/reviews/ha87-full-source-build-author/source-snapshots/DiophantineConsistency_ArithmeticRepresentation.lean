import DiophantineConsistency.Representation
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Arithmetic and graph constructors for explicit representations

These constructors supply syntax and finite witness blocks directly. They
do not extract a polynomial from `Dioph`, `IsPoly`, or a computability proof.
-/

namespace DiophantineConsistency

/-- Add one distinguished natural coordinate to an assignment. -/
def withOutput {σ : Type*} (v : σ → ℕ) (a : ℕ) : Option σ → ℕ
  | none => a
  | some i => v i

@[simp] theorem withOutput_none {σ : Type*} (v : σ → ℕ) (a : ℕ) :
    withOutput v a none = a := rfl
@[simp] theorem withOutput_some {σ : Type*} (v : σ → ℕ) (a : ℕ) (i : σ) :
    withOutput v a (some i) = v i := rfl

/-- An explicit representation of the graph of a natural-valued function. -/
abbrev GraphRep {σ : Type*} (f : (σ → ℕ) → ℕ) :=
  Rep (Option σ) (fun v => v none = f (v ∘ some))

namespace GraphRep

variable {σ τ : Type*} {f g : (σ → ℕ) → ℕ}

def constant (n : ℕ) : GraphRep (σ := σ) (fun _ => n) :=
  (Rep.equality (Expr.var none) (Expr.constant n)).ofIff (fun v => by
    simp only [Expr.eval_var, Expr.eval_constant, Int.natCast_inj])

def coordinate (i : σ) : GraphRep (fun v => v i) :=
  (Rep.equality (Expr.var none) (Expr.var (some i))).ofIff (fun v => by
    simp only [Expr.eval_var, Int.natCast_inj, Function.comp_apply])

/-- Precompose a represented function with a map of input coordinates. -/
def reindex (r : GraphRep f) (h : σ → τ) : GraphRep (fun v => f (v ∘ h)) :=
  (Rep.reindex r (Option.map h)).ofIff (fun _ => Iff.rfl)

end GraphRep

namespace Rep

variable {σ : Type*} {P : (Option σ → ℕ) → Prop} {f : (σ → ℕ) → ℕ}

/-- Substitute a represented function for one coordinate of a represented
predicate. Its value is an additional existential witness, constrained by
the function's graph. -/
def bindGraph (r : Rep (Option σ) P) (g : GraphRep f) :
    Rep σ (fun v => P (withOutput v (f v))) := by
  let index : Option σ → σ ⊕ Fin 1
    | none => .inr 0
    | some i => .inl i
  let combined := (r.conjunction g).reindex index
  refine (combined.existsBlock).ofIff ?_
  intro v
  have hval (a : Fin 1 → ℕ) : Sum.elim v a ∘ index = withOutput v (a 0) := by
    funext i
    cases i <;> rfl
  change (∃ a : Fin 1 → ℕ,
      P (Sum.elim v a ∘ index) ∧
        (Sum.elim v a ∘ index) none = f ((Sum.elim v a ∘ index) ∘ some)) ↔ _
  simp only [hval]
  constructor
  · rintro ⟨a, ha, h⟩
    change a 0 = f v at h
    simpa only [h] using ha
  · intro h
    exact ⟨fun _ => f v, h, rfl⟩

end Rep

namespace GraphRep

variable {σ : Type*} {f g : (σ → ℕ) → ℕ}

/-- Graphs are closed under addition, with all witnesses retained explicitly. -/
def add (r : GraphRep f) (s : GraphRep g) : GraphRep (fun v => f v + g v) := by
  let e : Rep (Option (Option (Option σ))) _ :=
    Rep.equality (Expr.var (some (some none)))
      (Expr.var (some none) + Expr.var none)
  let first := e.bindGraph (s.reindex (some ∘ some))
  let second := first.bindGraph (r.reindex some)
  refine second.ofIff ?_
  intro v
  change (v none : ℤ) = (f (v ∘ some) : ℤ) + (g (v ∘ some) : ℤ) ↔ _
  rw [← Int.natCast_add, Int.natCast_inj]

/-- Graphs are closed under multiplication. -/
def mul (r : GraphRep f) (s : GraphRep g) : GraphRep (fun v => f v * g v) := by
  let e : Rep (Option (Option (Option σ))) _ :=
    Rep.equality (Expr.var (some (some none)))
      (Expr.var (some none) * Expr.var none)
  let first := e.bindGraph (s.reindex (some ∘ some))
  let second := first.bindGraph (r.reindex some)
  refine second.ofIff ?_
  intro v
  change (v none : ℤ) = (f (v ∘ some) : ℤ) * (g (v ∘ some) : ℤ) ↔ _
  rw [← Int.natCast_mul, Int.natCast_inj]

end GraphRep

namespace ArithmeticRep

variable {σ : Type*}

/-- The natural inequality `a ≤ b` uses the slack `b-a`. -/
def le (a b : σ) : Rep σ (fun v => v a ≤ v b) where
  witnessCount := 1
  expression := Expr.var (.inl a) + Expr.var (.inr 0) - Expr.var (.inl b)
  correct v := by
    simp only [Expr.eval_sub, Expr.eval_add, Expr.eval_var, natAssignment_inl,
      natAssignment_inr, sub_eq_zero]
    constructor
    · intro h
      refine ⟨fun _ => v b - v a, ?_⟩
      dsimp only
      omega
    · rintro ⟨w, hw⟩
      have hw0 := Nat.zero_le (w 0)
      omega

/-- The natural inequality `a < b` uses the slack `b-a-1`. -/
def lt (a b : σ) : Rep σ (fun v => v a < v b) where
  witnessCount := 1
  expression := Expr.var (.inl a) + Expr.var (.inr 0) + Expr.constant 1 - Expr.var (.inl b)
  correct v := by
    simp only [Expr.eval_sub, Expr.eval_add, Expr.eval_var, Expr.eval_constant,
      natAssignment_inl, natAssignment_inr, sub_eq_zero]
    constructor
    · intro h
      refine ⟨fun _ => v b - v a - 1, ?_⟩
      dsimp only
      omega
    · rintro ⟨w, hw⟩
      have hw0 := Nat.zero_le (w 0)
      omega

/-- Divisibility uses its quotient as one natural witness, also when `a=0`. -/
def dvd (a b : σ) : Rep σ (fun v => v a ∣ v b) where
  witnessCount := 1
  expression := Expr.var (.inl a) * Expr.var (.inr 0) - Expr.var (.inl b)
  correct v := by
    simp only [Expr.eval_sub, Expr.eval_mul, Expr.eval_var, natAssignment_inl,
      natAssignment_inr, sub_eq_zero, ← Int.natCast_mul, Int.natCast_inj]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨fun _ => k, hk.symm⟩
    · rintro ⟨w, hw⟩
      exact ⟨w 0, hw.symm⟩

/-- Congruence modulo a natural number uses two nonnegative multiples.
The construction also handles modulus zero. -/
def modEq (a b modulus : σ) : Rep σ (fun v => Nat.ModEq (v modulus) (v a) (v b)) where
  witnessCount := 2
  expression :=
    (Expr.var (.inl a) + Expr.var (.inl modulus) * Expr.var (.inr 0)) -
      (Expr.var (.inl b) + Expr.var (.inl modulus) * Expr.var (.inr 1))
  correct v := by
    simp only [Expr.eval_sub, Expr.eval_add, Expr.eval_mul, Expr.eval_var,
      natAssignment_inl, natAssignment_inr, sub_eq_zero, ← Int.natCast_mul,
      ← Int.natCast_add, Int.natCast_inj]
    constructor
    · intro h
      refine ⟨fun i => if i.val = 0 then v b / v modulus else v a / v modulus, ?_⟩
      simp only [Fin.val_zero, Fin.val_one, one_ne_zero, if_true, if_false]
      have ha := Nat.mod_add_div (v a) (v modulus)
      have hb := Nat.mod_add_div (v b) (v modulus)
      change v a % v modulus = v b % v modulus at h
      omega
    · rintro ⟨w, hw⟩
      have h := congrArg (fun n => n % v modulus) hw
      simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod] using h

end ArithmeticRep

end DiophantineConsistency
