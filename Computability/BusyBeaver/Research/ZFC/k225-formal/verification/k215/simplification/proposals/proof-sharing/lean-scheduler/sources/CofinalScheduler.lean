import Init

/-!
A scheduler kernel for partial deterministic enumerators.

Only two successful-step facts are needed. At a boundary the candidate index
increases by one. Inside a candidate, the pending rank strictly decreases and
the index stays fixed. There is no bound on the pending rank after a refill.
The run equations are parameters, so client transition and run definitions
can remain literally unchanged.
-/
namespace SetTheory.BusyBeaver.ZFC.CofinalScheduler

universe u

structure Dynamics (S : Type u) where
  step : S → Option S
  run : Nat → S → Option S
  zero : ∀ s, run 0 s = some s
  succ : ∀ n s, run (n + 1) s =
    match step s with
    | some t => run n t
    | none => none

namespace Dynamics
variable {S : Type u} (M : Dynamics S)

def Halts (s : S) : Prop := ∃ n t, M.run n s = some t ∧ M.step t = none

theorem run_add : ∀ n m s t,
    M.run n s = some t → M.run (n + m) s = M.run m t
  | 0, m, s, t, h => by
      rw [M.zero] at h
      cases h
      simp only [Nat.zero_add]
  | n + 1, m, s, t, h => by
      rw [M.succ] at h
      cases hs : M.step s with
      | none => simp only [hs] at h; cases h
      | some v =>
          simp only [hs] at h
          rw [show n + 1 + m = (n + m) + 1 by omega, M.succ, hs]
          exact run_add n m v t h

theorem prepend {s t : S} (h : M.step s = some t) {n : Nat} {v : S}
    (hr : M.run n t = some v) : M.run (n + 1) s = some v := by
  rw [M.succ, h]
  exact hr

theorem halts_prepend {s t : S} (h : M.step s = some t) : M.Halts t → M.Halts s := by
  rintro ⟨n, v, hr, hv⟩
  exact ⟨n + 1, v, M.prepend h hr, hv⟩

theorem halts_of_run {s t : S} {n : Nat} (h : M.run n s = some t) :
    M.Halts t → M.Halts s := by
  rintro ⟨m, v, hr, hv⟩
  exact ⟨n + m, v, (M.run_add n m s t h).trans hr, hv⟩

theorem run_invariant (I : S → Prop)
    (preserves : ∀ s t, I s → M.step s = some t → I t) :
    ∀ n s t, I s → M.run n s = some t → I t
  | 0, s, t, hi, hr => by rw [M.zero] at hr; cases hr; exact hi
  | n + 1, s, t, hi, hr => by
      rw [M.succ] at hr
      cases hs : M.step s with
      | none => simp only [hs] at hr; cases hr
      | some v =>
          simp only [hs] at hr
          exact run_invariant I preserves n v t (preserves s v hi hs) hr

structure Laws (pending index : S → Nat) : Prop where
  advance : ∀ s t, M.step s = some t → pending s = 0 → index t = index s + 1
  descend : ∀ s t, M.step s = some t → pending s ≠ 0 →
    pending t < pending s ∧ index t = index s

variable {pending index : S → Nat} (L : M.Laws pending index)
include L

/-- Reach a requested later boundary or halt first, even from an active candidate. -/
theorem reach_or_halt (target : Nat) (s : S) (hle : index s ≤ target) :
    M.Halts s ∨ ∃ n t, M.run n s = some t ∧ pending t = 0 ∧ index t = target := by
  by_cases hp : pending s = 0
  · by_cases hi : index s = target
    · exact Or.inr ⟨0, s, M.zero s, hp, hi⟩
    · cases hs : M.step s with
      | none => exact Or.inl ⟨0, s, M.zero s, hs⟩
      | some t =>
          have ht := L.advance s t hs hp
          have hle' : index t ≤ target := by omega
          rcases reach_or_halt target t hle' with hh | ⟨n, v, hr, hv, hi⟩
          · exact Or.inl (M.halts_prepend hs hh)
          · exact Or.inr ⟨n + 1, v, M.prepend hs hr, hv, hi⟩
  · cases hs : M.step s with
    | none => exact Or.inl ⟨0, s, M.zero s, hs⟩
    | some t =>
        obtain ⟨hp', hi⟩ := L.descend s t hs hp
        have hle' : index t ≤ target := by omega
        rcases reach_or_halt target t hle' with hh | ⟨n, v, hr, hv, hi'⟩
        · exact Or.inl (M.halts_prepend hs hh)
        · exact Or.inr ⟨n + 1, v, M.prepend hs hr, hv, hi'⟩
termination_by (target - index s, pending s)
decreasing_by all_goals simp_wf; omega

/-- A fixed later target must work for each reachable payload at that boundary. -/
theorem complete_at (s : S) (target : Nat) (hge : index s ≤ target)
    (hit : ∀ n t, M.run n s = some t → pending t = 0 →
      index t = target → M.Halts t) : M.Halts s := by
  rcases M.reach_or_halt L target s hge with hh | ⟨n, t, hr, hp, hi⟩
  · exact hh
  · exact M.halts_of_run hr (hit n t hr hp hi)

end Dynamics
end SetTheory.BusyBeaver.ZFC.CofinalScheduler

