import BusyBeaver.ZFC.RMDag

/-!
A deterministic root simulation lifts from one step to finite halting runs.
The enumerators use different command formats but share this iteration argument.
-/

namespace SetTheory.BusyBeaver.ZFC.RMDag

/-- A root implementing a partial state transition halts exactly when its iteration does. -/
theorem iter_halts_iff {State : Type} {p : Prog}
    (step : State → Option State) (run : Nat → State → Option State) (encode : State → Regs)
    (run_zero : ∀ s, run 0 s = some s)
    (run_succ : ∀ n s, run (n + 1) s = match step s with
      | some s' => run n s'
      | none => none)
    (step_run : ∀ {s s'}, step s = some s' →
      Run p (.node p.root) (encode s) .normal (encode s'))
    (step_halt : ∀ {s}, step s = none → ∃ R', Run p (.node p.root) (encode s) .halt R')
    (s : State) :
    IterHalts p (encode s) ↔ ∃ n s', run n s = some s' ∧ step s' = none := by
  constructor
  · intro h
    suffices H : ∀ R, IterHalts p R → ∀ s, R = encode s →
        ∃ n s', run n s = some s' ∧ step s' = none from H _ h s rfl
    intro R hR
    induction hR with
    | halt R R' hrun =>
        intro s hs
        subst hs
        match he : step s with
        | none => exact ⟨0, s, run_zero s, he⟩
        | some s1 => cases (run_det hrun (step_run he)).1
    | next R R' hrun _ ih =>
        intro s hs
        subst hs
        match he : step s with
        | none =>
            obtain ⟨_, hh⟩ := step_halt he
            cases (run_det hrun hh).1
        | some s1 =>
            obtain ⟨n, s', h1, h2⟩ := ih s1 (run_det hrun (step_run he)).2
            exact ⟨n + 1, s', by rw [run_succ, he]; exact h1, h2⟩
  · rintro ⟨n, s', hrun, hstep⟩
    induction n generalizing s with
    | zero =>
        rw [run_zero] at hrun
        cases hrun
        obtain ⟨_, hh⟩ := step_halt hstep
        exact IterHalts.halt _ _ hh
    | succ n ih =>
        rw [run_succ] at hrun
        cases he : step s with
        | none => simp [he] at hrun
        | some s1 =>
            rw [he] at hrun
            exact IterHalts.next _ _ (step_run he) (ih s1 hrun)

end SetTheory.BusyBeaver.ZFC.RMDag
