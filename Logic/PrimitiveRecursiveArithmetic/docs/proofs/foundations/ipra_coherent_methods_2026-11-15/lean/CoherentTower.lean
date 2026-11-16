import Std

/-!
# Finite coherent lifting: host-level schema

A square-zero Taylor calculation supplies the local existence and uniqueness
fields.  This module proves that those *local* certificates suffice for
coherence and uniqueness at every finite level.  It does not assert the
algebraic hypotheses for a particular tower.
-/

namespace IPRAFramework

structure CoherentTower where
  Level : Nat → Type
  restrict : (n : Nat) → Level (n + 1) → Level n
  admissible : (n : Nat) → Level n → Prop
  lift : (n : Nat) → Level n → Level (n + 1)
  restrict_admissible : ∀ n x, admissible (n + 1) x → admissible n (restrict n x)
  lift_admissible : ∀ n x, admissible n x → admissible (n + 1) (lift n x)
  restrict_lift : ∀ n x, admissible n x → restrict n (lift n x) = x
  fiber_unique : ∀ n x y, admissible n x → admissible (n + 1) y →
    restrict n y = x → y = lift n x

namespace CoherentTower

def stage (T : CoherentTower) (seed : T.Level 0) : (n : Nat) → T.Level n
  | 0 => seed
  | n + 1 => T.lift n (stage T seed n)

def toBase (T : CoherentTower) : (n : Nat) → T.Level n → T.Level 0
  | 0, x => x
  | n + 1, x => toBase T n (T.restrict n x)

variable (T : CoherentTower) {seed : T.Level 0}

theorem stage_admissible (hs : T.admissible 0 seed) (n : Nat) :
    T.admissible n (T.stage seed n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact T.lift_admissible n _ ih

theorem coherent (hs : T.admissible 0 seed) (n : Nat) :
    T.restrict n (T.stage seed (n + 1)) = T.stage seed n :=
  T.restrict_lift n _ (T.stage_admissible hs n)

theorem stage_base (hs : T.admissible 0 seed) (n : Nat) :
    T.toBase n (T.stage seed n) = seed := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change T.toBase n (T.restrict n (T.stage seed (n + 1))) = seed
      rw [T.coherent hs n]
      exact ih

/-- Local fiber uniqueness implies finite global uniqueness over the seed. -/
theorem unique (hs : T.admissible 0 seed) (n : Nat) (x : T.Level n)
    (hx : T.admissible n x) (hb : T.toBase n x = seed) : x = T.stage seed n := by
  induction n with
  | zero => exact hb
  | succ n ih =>
      have hr : T.restrict n x = T.stage seed n :=
        ih (T.restrict n x) (T.restrict_admissible n x hx) hb
      exact T.fiber_unique n (T.stage seed n) x (T.stage_admissible hs n) hx hr

end CoherentTower

end IPRAFramework

#print axioms IPRAFramework.CoherentTower.coherent
#print axioms IPRAFramework.CoherentTower.unique
