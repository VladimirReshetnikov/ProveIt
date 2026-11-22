import Std

namespace IPRAComplexity

/-- Nonnegative-coefficient polynomials; resource bounds are syntax, not oracles. -/
inductive Polynomial where
  | const : Nat → Polynomial
  | var : Polynomial
  | add : Polynomial → Polynomial → Polynomial
  | mul : Polynomial → Polynomial → Polynomial
  deriving Repr

def Polynomial.eval : Polynomial → Nat → Nat
  | .const c, _ => c
  | .var, n => n
  | .add p q, n => p.eval n + q.eval n
  | .mul p q, n => p.eval n * q.eval n

def Polynomial.subst : Polynomial → Polynomial → Polynomial
  | .const c, _ => .const c
  | .var, q => q
  | .add p₁ p₂, q => .add (p₁.subst q) (p₂.subst q)
  | .mul p₁ p₂, q => .mul (p₁.subst q) (p₂.subst q)

theorem Polynomial.eval_subst (p q : Polynomial) (n : Nat) :
    (p.subst q).eval n = p.eval (q.eval n) := by
  induction p with
  | const c => rfl
  | var => rfl
  | add p₁ p₂ ih₁ ih₂ => simp [subst, eval, ih₁, ih₂]
  | mul p₁ p₂ ih₁ ih₂ => simp [subst, eval, ih₁, ih₂]

theorem Polynomial.eval_mono (p : Polynomial) {m n : Nat} (h : m ≤ n) :
    p.eval m ≤ p.eval n := by
  induction p with
  | const c => exact Nat.le_refl c
  | var => exact h
  | add p q ihp ihq => exact Nat.add_le_add ihp ihq
  | mul p q ihp ihq => exact Nat.mul_le_mul ihp ihq

/-- Extensional many-one reduction. Its map still needs a machine implementation. -/
structure Reduction (A B : Nat → Prop) where
  map : Nat → Nat
  correct : ∀ x, A x ↔ B (map x)

def Reduction.id (A : Nat → Prop) : Reduction A A where
  map := fun x => x
  correct := fun _ => Iff.rfl

def Reduction.comp {A B C : Nat → Prop}
    (f : Reduction A B) (g : Reduction B C) : Reduction A C where
  map := fun x => g.map (f.map x)
  correct := fun x => (f.correct x).trans (g.correct (f.map x))

/-- Polynomial output-size certificate, separated from the cost of evaluating a map. -/
structure PolyMap (size : Nat → Nat) where
  map : Nat → Nat
  bound : Polynomial
  size_le : ∀ x, size (map x) ≤ bound.eval (size x)

def PolyMap.comp {size : Nat → Nat} (f g : PolyMap size) : PolyMap size where
  map := fun x => g.map (f.map x)
  bound := g.bound.subst f.bound
  size_le := by
    intro x
    rw [Polynomial.eval_subst]
    exact Nat.le_trans (g.size_le _) (g.bound.eval_mono (f.size_le x))

/-- Cost accounting for a fixed sequential implementation.

`ticks` is a supplied operational cost, not a runtime inferred from a Lean function.
To use this record for machine complexity, separately prove that it equals or bounds
the step count of that implementation. Composition here counts the two calls; a real
machine compiler must add its explicit copying/control overhead polynomial.
-/
structure PolyCost (size : Nat → Nat) extends PolyMap size where
  ticks : Nat → Nat
  timeBound : Polynomial
  ticks_le : ∀ x, ticks x ≤ timeBound.eval (size x)

def PolyCost.comp {size : Nat → Nat} (f g : PolyCost size) : PolyCost size where
  toPolyMap := f.toPolyMap.comp g.toPolyMap
  ticks := fun x => f.ticks x + g.ticks (f.map x)
  timeBound := .add f.timeBound (g.timeBound.subst f.bound)
  ticks_le := by
    intro x
    simp only [Polynomial.eval, Polynomial.eval_subst]
    exact Nat.add_le_add (f.ticks_le x)
      (Nat.le_trans (g.ticks_le _) (g.timeBound.eval_mono (f.size_le x)))

/-- Polynomial reduction data whose cost has the explicit interpretation above. -/
structure PolyReduction (size : Nat → Nat) (A B : Nat → Prop)
    extends PolyCost size where
  correct : ∀ x, A x ↔ B (map x)

def PolyReduction.comp {size : Nat → Nat} {A B C : Nat → Prop}
    (f : PolyReduction size A B) (g : PolyReduction size B C) :
    PolyReduction size A C where
  toPolyCost := f.toPolyCost.comp g.toPolyCost
  correct := fun x => (f.correct x).trans (g.correct (f.map x))

end IPRAComplexity
