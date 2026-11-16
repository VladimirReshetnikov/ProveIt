import Std.Tactic

/-! A model-agnostic bounded stuttering argument.  No claim is made here
about PA196, representations, or first-order arithmetic. -/
namespace ReverseStuttering

variable {S M : Type}

def run (f : S → S) (x : S) : Nat → S
  | 0 => x
  | n + 1 => f (run f x n)

theorem run_add (f : S → S) (x : S) (a b : Nat) :
    run f x (a + b) = run f (run f x a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change f (run f x (a + b)) = f (run f (run f x a) b)
    rw [ih]

variable (nextS : S → S) (nextM : M → M)
variable (sourceHalt : S → Prop) (machineHalt : M → Prop)
variable (related : S → M → Prop)

/-- If a physical control has halted, it remains halted at every later time. -/
theorem halt_persists
    (habsorb : ∀ m, machineHalt m → machineHalt (nextM m))
    (m : M) (h : machineHalt m) (n : Nat) :
    machineHalt (run nextM m n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact habsorb _ ih

/-- A source prefix can be expanded into at least as many physical steps,
provided each of its nonhalting instructions admits a positive segment. -/
theorem expand_prefix
    (s₀ : S) (m₀ : M) (hinit : related s₀ m₀)
    (hstep : ∀ s m, related s m → ¬ sourceHalt s →
      ∃ k, 0 < k ∧ related (nextS s) (run nextM m k))
    (n : Nat) (hs : ∀ j < n, ¬ sourceHalt (run nextS s₀ j)) :
    ∃ k, n ≤ k ∧ related (run nextS s₀ n) (run nextM m₀ k) := by
  induction n with
  | zero => exact ⟨0, Nat.le_refl _, hinit⟩
  | succ n ih =>
    obtain ⟨k, hkn, hr⟩ := ih (fun j hj => hs j (by omega))
    obtain ⟨d, hd, hnext⟩ := hstep _ _ hr (hs n (by omega))
    refine ⟨k + d, by omega, ?_⟩
    simpa only [run, run_add] using hnext

/-- If the deterministic physical run halts by time `t`, then some source
configuration at index at most `t` is halted. `hboundary` rules out a
halting physical boundary corresponding to a nonhalting source state. -/
theorem source_halts_by_physical_time
    (s₀ : S) (m₀ : M) (hinit : related s₀ m₀)
    (hstep : ∀ s m, related s m → ¬ sourceHalt s →
      ∃ k, 0 < k ∧ related (nextS s) (run nextM m k))
    (hboundary : ∀ s m, related s m → ¬ sourceHalt s → ¬ machineHalt m)
    (habsorb : ∀ m, machineHalt m → machineHalt (nextM m))
    (t : Nat) (ht : machineHalt (run nextM m₀ t)) :
    ∃ j ≤ t, sourceHalt (run nextS s₀ j) := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hs : ∀ j ≤ t, ¬ sourceHalt (run nextS s₀ j) := by
    intro j hj h
    exact hnone ⟨j, hj, h⟩
  obtain ⟨k, htk, hr⟩ := expand_prefix nextS nextM sourceHalt related s₀ m₀ hinit hstep t
    (fun j hj => hs j (by omega))
  have hh : machineHalt (run nextM m₀ k) := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htk
    rw [run_add]
    exact halt_persists nextM machineHalt habsorb _ ht d
  exact hboundary _ _ hr (hs t (Nat.le_refl t)) hh

end ReverseStuttering

#print axioms ReverseStuttering.source_halts_by_physical_time
#print axioms ReverseStuttering.expand_prefix

/-- A positive test: the physical run makes two steps for each source step. -/
example : ∃ j ≤ 4, 2 ≤ ReverseStuttering.run Nat.succ 0 j := by
  refine ReverseStuttering.source_halts_by_physical_time Nat.succ Nat.succ
    (fun s => 2 ≤ s) (fun m => 4 ≤ m) (fun s m => m = 2*s)
    0 0 rfl ?_ ?_ ?_ 4 ?_
  · intro s m hr hn
    refine ⟨2, by decide, ?_⟩
    simp only [ReverseStuttering.run]
    omega
  · intro s m hr hn hm
    omega
  · intro m hm
    omega
  · decide
