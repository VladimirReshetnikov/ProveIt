import Std

/-!
# Bounded descent: host-level core

These are Lean theorems about finite iteration.  They are not, by themselves,
object-iPRA derivations.  For that endpoint all data must be fixed PR symbols
and `valid` must be Booleanized; see ObjectComposition and FORMALIZATION.md.
-/

namespace IPRAFramework

/-- Every operation is fixed in advance; no universal program evaluator. -/
structure RankedProcess (S : Type) where
  step : S → S
  terminal : S → Bool
  valid : S → Prop
  rank : S → Nat
  preserve : ∀ s, valid s → valid (step s)
  absorb : ∀ s, valid s → terminal s = true → step s = s
  decrease : ∀ s, valid s → terminal s = false → rank (step s) < rank s

namespace RankedProcess

variable {S : Type} (p : RankedProcess S)

def run (p : RankedProcess S) (s : S) : Nat → S
  | 0 => s
  | n + 1 => p.step (run p s n)

@[simp] theorem run_zero (s : S) : p.run s 0 = s := rfl

@[simp] theorem run_succ (s : S) (n : Nat) :
    p.run s (n + 1) = p.step (p.run s n) := rfl

theorem valid_run {s : S} (hs : p.valid s) (n : Nat) : p.valid (p.run s n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact p.preserve _ ih

/-- The Boolean disjunction is the invariant used by the arithmetic proof. -/
theorem budget {s : S} (hs : p.valid s) (n : Nat) :
    p.terminal (p.run s n) = true ∨ p.rank (p.run s n) + n ≤ p.rank s := by
  induction n with
  | zero => exact Or.inr (by simp)
  | succ n ih =>
      have hv := p.valid_run hs n
      cases ht : p.terminal (p.run s n) with
      | true =>
          left
          rw [run_succ, p.absorb _ hv ht]
          exact ht
      | false =>
          have hb : p.rank (p.run s n) + n ≤ p.rank s := by
            rcases ih with h | h
            · simp [ht] at h
            · exact h
          have hd := p.decrease _ hv ht
          right
          rw [run_succ]
          omega

/-- `rank s` steps suffice; a nonterminal rank-zero state is impossible. -/
theorem terminates {s : S} (hs : p.valid s) :
    p.terminal (p.run s (p.rank s)) = true := by
  have hb := p.budget hs (p.rank s)
  cases ht : p.terminal (p.run s (p.rank s)) with
  | true => rfl
  | false =>
      have hd := p.decrease _ (p.valid_run hs (p.rank s)) ht
      rcases hb with h | h
      · simp [ht] at h
      · omega

/-- Any invariant is preserved, including a reconstruction equation. -/
theorem invariant {J : S → Prop}
    (hj : ∀ t, p.valid t → J t → J (p.step t))
    {s : S} (hs : p.valid s) (hjs : J s) (n : Nat) : J (p.run s n) := by
  induction n with
  | zero => exact hjs
  | succ n ih => exact hj _ (p.valid_run hs n) ih

theorem terminal_stable {s : S} (hs : p.valid s)
    (ht : p.terminal s = true) (n : Nat) : p.run s n = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, p.absorb _ hs ht]

end RankedProcess

/-- A rational decrease inequality implies an integral rank drop above B.
The caller separately derives this inequality from its height estimate. -/
theorem contraction_decreases (a b C B h h' : Nat)
    (hab : a < b) (hB : C ≤ (b - a) * B)
    (hh : B < h) (hstep : b * h' ≤ a * h + C) : h' < h := by
  have hp : 0 < b - a := Nat.sub_pos_of_lt hab
  have hmul : (b - a) * B < (b - a) * h := Nat.mul_lt_mul_of_pos_left hh hp
  have hc : C < (b - a) * h := Nat.lt_of_le_of_lt hB hmul
  have hsplit : a * h + (b - a) * h = b * h := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt hab)]
  have hstrict : b * h' < b * h := by omega
  by_cases hlt : h' < h
  · exact hlt
  · have hm : b * h ≤ b * h' := Nat.mul_le_mul_left b (by omega)
    omega

end IPRAFramework

#print axioms IPRAFramework.RankedProcess.terminates
#print axioms IPRAFramework.contraction_decreases
