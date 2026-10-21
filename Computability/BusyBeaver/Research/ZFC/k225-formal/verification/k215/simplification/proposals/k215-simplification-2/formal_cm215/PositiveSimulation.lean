import Std

/-!
A reusable positive-step transfer theorem for deterministic computations.
No Turing-machine-specific definitions and no mathlib imports are used.
Halting configurations may be totalized by making the next operation fix them.
A transition of the first computation may take any positive finite number
of transitions of the second computation.  Its halting predicate only needs
to be preserved by one next step; the proof does not assume a uniform bound.
-/
namespace PositiveSimulation

universe u v

def iter {A : Type u} (next : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => next (iter next n a)

theorem iter_add {A : Type u} (next : A → A) (m n : Nat) (a : A) :
    iter next (m + n) a = iter next n (iter next m a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change next (iter next (m + n) a) = next (iter next n (iter next m a))
      exact congrArg next ih

theorem stable_iter {A : Type u} (next : A → A) (P : A → Prop)
    (stable : ∀ a, P a → P (next a)) {a : A} (ha : P a) (n : Nat) :
    P (iter next n a) := by
  induction n with
  | zero => exact ha
  | succ n ih => exact stable _ ih

/-- A positive local simulation gives cofinal synchronization times.
The relation can contain the entire source invariant, so no separate
reachable-state predicate or trace-history argument is required. -/
theorem synchronized {A : Type u} {B : Type v} (f : A → A) (g : B → B)
    (R : A → B → Prop)
    (sim : ∀ a b, R a b → ∃ j, R (f a) (iter g (j + 1) b))
    {a : A} {b : B} (hab : R a b) (n : Nat) :
    ∃ k, n ≤ k ∧ R (iter f n a) (iter g k b) := by
  induction n with
  | zero => exact ⟨0, Nat.le_refl 0, hab⟩
  | succ n ih =>
      obtain ⟨k, hnk, hr⟩ := ih
      obtain ⟨j, hs⟩ := sim _ _ hr
      refine ⟨k + (j + 1), by omega, ?_⟩
      change R (f (iter f n a)) (iter g (k + (j + 1)) b)
      rw [iter_add]
      exact hs

/-- Eventual halting is equivalent at related configurations.
Only the target halting predicate needs stability. The crucial strict
progress premise is encoded as j+1 in sim, rather than a possibly empty run. -/
theorem halts_iff {A : Type u} {B : Type v} (f : A → A) (g : B → B)
    (PA : A → Prop) (PB : B → Prop) (R : A → B → Prop)
    (sim : ∀ a b, R a b → ∃ j, R (f a) (iter g (j + 1) b))
    (halt : ∀ a b, R a b → (PA a ↔ PB b))
    (stable : ∀ b, PB b → PB (g b))
    {a : A} {b : B} (hab : R a b) :
    (∃ n, PA (iter f n a)) ↔ ∃ n, PB (iter g n b) := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨k, _, hk⟩ := synchronized f g R sim hab n
    exact ⟨k, (halt _ _ hk).mp hn⟩
  · rintro ⟨n, hn⟩
    obtain ⟨k, hnk, hk⟩ := synchronized f g R sim hab n
    have hp := stable_iter g PB stable hn (k - n)
    have he : n + (k - n) = k := by omega
    have ht : PB (iter g k b) := by
      rw [← iter_add, he] at hp
      exact hp
    exact ⟨n, (halt _ _ hk).mpr ht⟩

#print axioms halts_iff
end PositiveSimulation
