import Std

/-!
A quantifier counterexample for candidate-search completeness.

Every fixed payload has cofinally many candidates that would halt on that
payload.  Nevertheless the actual scheduler never halts, because each
completed candidate changes the payload before the next candidate runs.

This file is independent of the ProveIt endpoint and uses no axioms.
-/

namespace FrontierCounterexample

def parity : Nat → Bool
  | 0 => false
  | n + 1 => !parity n

abbrev State := Nat × Bool

/-- Every successful step is already a boundary-to-boundary step. -/
def step (s : State) : Option State :=
  if s.2 = parity s.1 then some (s.1 + 1, !s.2) else none

def run : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => (step s).bind (run n)

def Halts (s : State) : Prop :=
  ∃ n t, run n s = some t ∧ step t = none

theorem successful_step_advances {s t : State} (h : step s = some t) :
    t.1 = s.1 + 1 := by
  unfold step at h
  split at h
  · cases h; rfl
  · cases h

/-- The weakened, payload-wise cofinality assumption holds. -/
theorem payloadwise_cofinal (b : Bool) (N : Nat) :
    ∃ k, N ≤ k ∧ step (k, b) = none := by
  by_cases h : b = parity N
  · refine ⟨N + 1, Nat.le_succ N, ?_⟩
    have hn : b ≠ !parity N := by
      intro he
      have hb : b = !b := he.trans (congrArg Bool.not h.symm)
      cases b <;> cases hb
    exact if_neg hn
  · exact ⟨N, Nat.le_refl N, if_neg h⟩

theorem step_aligned (k : Nat) :
    step (k, parity k) = some (k + 1, parity (k + 1)) := if_pos rfl

theorem run_aligned (n k : Nat) :
    run n (k, parity k) = some (k + n, parity (k + n)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    change (step (k, parity k)).bind (run n) = _
    rw [step_aligned]
    change run n (k + 1, parity (k + 1)) = _
    rw [ih]
    have he : (k + 1) + n = k + (n + 1) :=
      (Nat.add_assoc k 1 n).trans (congrArg (Nat.add k) (Nat.add_comm 1 n))
    exact congrArg (fun j => some (j, parity j)) he

/-- The actual payload remains aligned with the current candidate forever. -/
theorem aligned_never_halts (k : Nat) : ¬ Halts (k, parity k) := by
  rintro ⟨n, t, ht, hh⟩
  rw [run_aligned] at ht
  cases ht
  have impossible := (step_aligned (k + n)).symm.trans hh
  cases impossible

theorem no_uniform_candidate (k : Nat) :
    ¬ (∀ b : Bool, step (k, b) = none) := by
  intro h
  have hh := h (parity k)
  have impossible := (step_aligned k).symm.trans hh
  cases impossible

#print axioms payloadwise_cofinal
#print axioms aligned_never_halts
#print axioms no_uniform_candidate

end FrontierCounterexample
