import PA194CommandRun
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PA194CommandEquiv
open M6.Source PA194CommandRun

def Halts (s : State) : Prop := ∃ k s', PA194CommandRun.run k s = some s' ∧ advance s' = none

theorem run_sound_lower (k : Nat) {s s' : State} (h : PA194CommandRun.run k s = some s') :
    ∃ n, k ≤ n ∧ CycleSteps PA194SourceProgram.sites n (config s) (config s') := by
  induction k generalizing s with
  | zero =>
    simp only [PA194CommandRun.run,Option.some.injEq] at h
    subst s'
    exact ⟨0,by omega,CycleSteps.refl _⟩
  | succ k ih =>
    cases ha : advance s with
    | none => simp [PA194CommandRun.run,ha] at h
    | some mid =>
      simp only [PA194CommandRun.run,ha,Option.bind_some] at h
      obtain ⟨n,hn,hstep⟩ := advance_sound ha
      obtain ⟨m,hm,hrest⟩ := ih h
      exact ⟨n+m,by omega,hstep.append hrest⟩

theorem nohalt_runs {s : State} (h : ¬ Halts s) : ∀ k, ∃ s', PA194CommandRun.run k s = some s' := by
  intro k
  induction k with
  | zero => exact ⟨s,rfl⟩
  | succ k ih =>
    obtain ⟨mid,hm⟩ := ih
    cases ha : advance mid with
    | none => exact False.elim (h ⟨k,mid,hm,ha⟩)
    | some dest =>
      -- Iteration is written in forward-recursive order, so append one step.
      have happend : ∀ n x y, PA194CommandRun.run n x = some y →
          PA194CommandRun.run (n+1) x = (advance y) := by
        intro n
        induction n with
        | zero =>
          intro x y hxy
          simp only [PA194CommandRun.run,Option.some.injEq] at hxy
          subst y
          simp [PA194CommandRun.run]
        | succ n ih' =>
          intro x y hxy
          cases hx : advance x with
          | none => simp [PA194CommandRun.run,hx] at hxy
          | some z =>
            simp only [PA194CommandRun.run,hx,Option.bind_some] at hxy
            simpa only [PA194CommandRun.run,hx,Option.bind_some] using ih' z y hxy
      exact ⟨dest,by rw [happend k s mid hm,ha]⟩

theorem nohalt_source {s : State} (h : ¬ Halts s) :
    ¬ CycleHalts PA194SourceProgram.sites (config s) := by
  intro hh
  obtain ⟨m,hm⟩ := hh
  obtain ⟨s',hr⟩ := nohalt_runs h (m+1)
  obtain ⟨n,hn,hsteps⟩ := run_sound_lower (m+1) hr
  have hstable : cycleStep PA194SourceProgram.sites
        (cycleRun PA194SourceProgram.sites m (config s)) =
          cycleRun PA194SourceProgram.sites m (config s) := by
    cases hz : cycleRun PA194SourceProgram.sites m (config s) with
    | mk control registers =>
      cases control <;> simp_all [cycleStep,restart,step]
  have he : n = m+(n-m) := by omega
  have hf := hsteps.eq_run
  rw [he,cycleRun_add,cycleRun_stable hstable] at hf
  have hc := congrArg Configuration.control hf
  change (cycleRun PA194SourceProgram.sites m (config s)).control = .at 25 at hc
  rw [hm] at hc
  cases hc

theorem halts_iff (s : State) : Halts s ↔ CycleHalts PA194SourceProgram.sites (config s) := by
  constructor
  · rintro ⟨k,s',hk,hh⟩
    exact scheduler_halts_source k hk hh
  · intro hh
    by_cases h : Halts s
    · exact h
    · exact False.elim (nohalt_source h hh)

#print axioms halts_iff
end PA194CommandEquiv
