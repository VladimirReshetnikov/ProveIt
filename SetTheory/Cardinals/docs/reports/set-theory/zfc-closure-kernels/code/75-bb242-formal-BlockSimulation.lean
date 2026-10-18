import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace PositiveBlocks
universe u
variable {α : Type u}

def run (f : α → α) : Nat → α → α
  | 0, c => c
  | n + 1, c => f (run f n c)

theorem run_add (f : α → α) (m n : Nat) (c : α) :
    run f (m + n) c = run f n (run f m c) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f ih

theorem fixed_run (f : α → α) (c : α) (h : f c = c) (n : Nat) :
    run f n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, h]

def Halts (f : α → α) (terminal : α → Prop) (c : α) : Prop :=
  ∃ n, terminal (run f n c)

theorem after_positive (f : α → α) (terminal : α → Prop)
    (stable : ∀ c, terminal c → f c = c)
    (c : α) (n k : Nat) (hk : 0 < k)
    (h : terminal (run f (n + 1) c)) :
    terminal (run f n (run f k c)) := by
  rw [← run_add]
  have heq : k + n = (n + 1) + (k - 1) := by omega
  rw [heq, run_add, fixed_run f _ (stable _ h)]
  exact h

theorem transport (f g : α → α) (terminal : α → Prop)
    (stable : ∀ c, terminal c → f c = c) (J : α → Prop)
    (blocks : ∀ c, J c → ∃ k l d,
      0 < k ∧ 0 < l ∧ run f k c = d ∧ run g l c = d ∧ J d)
    (c : α) (hc : J c) : Halts f terminal c → Halts g terminal c := by
  rintro ⟨n, hn⟩
  induction n generalizing c with
  | zero => exact ⟨0, hn⟩
  | succ n ih =>
      obtain ⟨k, l, d, hk, _, hf, hg, hd⟩ := blocks c hc
      have hn' : terminal (run f n d) := by
        rw [← hf]
        exact after_positive f terminal stable c n k hk hn
      obtain ⟨m, hm⟩ := ih d hd hn'
      exact ⟨l + m, by rw [run_add, hg]; exact hm⟩

theorem halting_iff (f g : α → α) (terminal : α → Prop)
    (stable_f : ∀ c, terminal c → f c = c)
    (stable_g : ∀ c, terminal c → g c = c) (J : α → Prop)
    (blocks : ∀ c, J c → ∃ k l d,
      0 < k ∧ 0 < l ∧ run f k c = d ∧ run g l c = d ∧ J d)
    (c : α) (hc : J c) : Halts f terminal c ↔ Halts g terminal c := by
  constructor
  · exact transport f g terminal stable_f J blocks c hc
  · apply transport g f terminal stable_g J _ c hc
    intro a ha
    obtain ⟨k, l, d, hk, hl, hf, hg, hd⟩ := blocks a ha
    exact ⟨l, k, d, hl, hk, hg, hf, hd⟩
end PositiveBlocks
