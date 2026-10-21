import Std

/-! A reusable positive-stuttering transfer lemma. No machine-specific axioms. -/
namespace PositiveStuttering

def run {A : Type} (f : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => f (run f n a)

@[simp] theorem run_zero {A : Type} (f : A → A) (a : A) : run f 0 a = a := rfl
@[simp] theorem run_succ {A : Type} (f : A → A) (n : Nat) (a : A) :
    run f (n+1) a = f (run f n a) := rfl

theorem run_add {A : Type} (f : A → A) (n m : Nat) (a : A) :
    run f (n + m) a = run f m (run f n a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    change f (run f (n+m) a) = f (run f m (run f n a))
    rw [ih]

theorem invariant_run {A : Type} (f : A → A) (I : A → Prop)
    (closed : ∀ a, I a → I (f a)) (a : A) (ha : I a) (n : Nat) :
    I (run f n a) := by
  induction n with
  | zero => exact ha
  | succ n ih => exact closed _ ih

/-- Positive macro lengths, with no uniform upper bound, suffice for equihalting.
The totalized target's terminal predicate must persist. -/
theorem equihalting {A B : Type} (f : A → A) (g : B → B) (φ : A → B)
    (I HA : A → Prop) (HB : B → Prop) (a : A)
    (init : I a) (closed : ∀ x, I x → I (f x))
    (terminal : ∀ y, HB y → HB (g y))
    (reflect : ∀ x, HB (φ x) ↔ HA x)
    (simulate : ∀ x, I x → ∃ k, 1 ≤ k ∧ run g k (φ x) = φ (f x)) :
    (∃ n, HA (run f n a)) ↔ (∃ n, HB (run g n (φ a))) := by
  have schedule : ∀ n, ∃ t, n ≤ t ∧ run g t (φ a) = φ (run f n a) := by
    intro n
    induction n with
    | zero => exact ⟨0, Nat.le_refl _, rfl⟩
    | succ n ih =>
      obtain ⟨t, ht, he⟩ := ih
      obtain ⟨k, hk, hs⟩ := simulate _ (invariant_run f I closed a init n)
      refine ⟨t+k, by omega, ?_⟩
      rw [run_add, he, hs]
      rfl
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨t, _, he⟩ := schedule n
    exact ⟨t, he ▸ (reflect _).mpr hn⟩
  · rintro ⟨n, hn⟩
    obtain ⟨t, ht, he⟩ := schedule n
    have hp := invariant_run g HB terminal (run g n (φ a)) hn (t-n)
    rw [← run_add] at hp
    have htn : n + (t-n) = t := by omega
    rw [htn, he] at hp
    exact ⟨n, (reflect _).mp hp⟩

#print axioms equihalting
end PositiveStuttering
