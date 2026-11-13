module
public import M6.Source.ParsedCommandTransfer
public import M6.Source.CommandHalting
public import M6.Source.EnumerationSchedule
public import M6.Source.SchedulerSafety
@[expose] public section
namespace M6.Source.CommandRunTransfer
open Enumeration

variable (hstep : ∀ (n l : Nat) (s out : CommandStore),
  commandEval (parse (FetchDispatch.seed n l)).command s = some out →
  ∃ m, 0 < m ∧ CycleSteps exactSites m (commandConfig 0 n l 0 s)
    (commandConfig 0 (FetchDispatch.nextN n l) (parse (FetchDispatch.seed n l)).next 0 out))

private theorem halts_of_prefix (hs : CycleSteps sites n a b) (hh : CycleHalts sites b) :
    CycleHalts sites a := by
  obtain ⟨m,hm⟩ := hh
  exact ⟨n+m,by simpa only [cycleRun_add,hs.eq_run] using hm⟩

include hstep
/-- Exhausting a continuation word either reaches L=0 with its exact arithmetic
result or reaches the real source halt. The induction is on the encoded pointer. -/
theorem continuation_outcome (l n : Nat) (s : CommandStore) :
    match commandsEval (residual l) s with
    | none => CycleHalts exactSites (commandConfig 0 n l 0 s)
    | some out => ∃ m, CycleSteps exactSites m (commandConfig 0 n l 0 s) (commandConfig 0 n 0 0 out) := by
  induction l using Nat.strongRecOn generalizing n s with
  | ind l ih =>
    cases l with
    | zero =>
      simp only [residual,commandsEval]
      exact ⟨0,CycleSteps.refl _⟩
    | succ l =>
      rw [residual,commandsEval]
      cases he : commandEval (parse l).command s with
      | none =>
        simp only [Option.bind_none]
        apply parsed_command_halts n (l+1) s
        simpa [FetchDispatch.seed] using he
      | some mid =>
        simp only [Option.bind_some]
        have he' : commandEval (parse (FetchDispatch.seed n (l+1))).command s = some mid := by
          simpa [FetchDispatch.seed] using he
        obtain ⟨m,hm,hs⟩ := hstep n (l+1) s mid he'
        simp [FetchDispatch.seed,FetchDispatch.nextN] at hs
        have hn := ih (parse l).next (Nat.lt_succ_of_le (parse_next_le l)) n mid
        cases hr : commandsEval (residual (parse l).next) mid with
        | none =>
          simp only [hr] at hn ⊢
          exact halts_of_prefix hs hn
        | some out =>
          simp only [hr] at hn ⊢
          obtain ⟨k,hk⟩ := hn
          exact ⟨m+k,hs.append hk⟩

/-- Fresh N executes exactly word N, incrementing the fresh counter once. -/
theorem word_outcome (n : Nat) (s : CommandStore) :
    match commandsEval (word n) s with
    | none => CycleHalts exactSites (commandConfig 0 n 0 0 s)
    | some out => ∃ m, CycleSteps exactSites m (commandConfig 0 n 0 0 s) (commandConfig 0 (n+1) 0 0 out) := by
  rw [word,commandsEval]
  cases he : commandEval (parse n).command s with
  | none =>
    simp only [Option.bind_none]
    apply parsed_command_halts n 0 s
    simpa [FetchDispatch.seed] using he
  | some mid =>
    simp only [Option.bind_some]
    have he' : commandEval (parse (FetchDispatch.seed n 0)).command s = some mid := by
      simpa [FetchDispatch.seed] using he
    obtain ⟨m,hm,hs⟩ := hstep n 0 s mid he'
    simp [FetchDispatch.seed,FetchDispatch.nextN] at hs
    have hn := continuation_outcome hstep (parse n).next (n+1) mid
    cases hr : commandsEval (residual (parse n).next) mid with
    | none =>
      simp only [hr] at hn ⊢
      exact halts_of_prefix hs hn
    | some out =>
      simp only [hr] at hn ⊢
      obtain ⟨k,hk⟩ := hn
      exact ⟨m+k,hs.append hk⟩

/-- Every finite complete schedule is actually executed unless a preceding
arithmetic command already caused the real source halt. -/
theorem schedule_outcome (n : Nat) :
    match commandsEval (schedule n) commandInitial with
    | none => CycleHalts exactSites (commandConfig 0 0 0 0 commandInitial)
    | some out => ∃ m, CycleSteps exactSites m (commandConfig 0 0 0 0 commandInitial)
        (commandConfig 0 n 0 0 out) := by
  induction n with
  | zero => exact ⟨0,CycleSteps.refl _⟩
  | succ n ih =>
    rw [schedule_succ,commandsEval_append]
    cases he : commandsEval (schedule n) commandInitial with
    | none =>
      simp only [he,Option.bind_none] at ih ⊢
      exact ih
    | some mid =>
      simp only [he,Option.bind_some] at ih ⊢
      obtain ⟨m,hs⟩ := ih
      have hw := word_outcome hstep n mid
      cases hr : commandsEval (word n) mid with
      | none =>
        simp only [hr] at hw ⊢
        exact halts_of_prefix hs hw
      | some out =>
        simp only [hr] at hw ⊢
        obtain ⟨k,hk⟩ := hw
        exact ⟨m+k,hs.append hk⟩

/-- A failed finite arithmetic schedule prefix forces actual source halting;
an earlier halt is accepted rather than being silently bypassed. -/
theorem prefix_halts (n : Nat) (p rest : List Command) (hp : word n = p++rest)
    (hbad : commandsEval (schedule n++p) commandInitial = none) :
    CycleHalts exactSites (commandConfig 0 0 0 0 commandInitial) := by
  have hs := schedule_outcome hstep n
  cases he : commandsEval (schedule n) commandInitial with
  | none => simpa only [he] using hs
  | some mid =>
    simp only [he] at hs
    obtain ⟨m,hm⟩ := hs
    have hpbad : commandsEval p mid = none := by
      simpa only [commandsEval_append,he,Option.bind_some] using hbad
    have hwbad : commandsEval (word n) mid = none := by
      rw [hp,commandsEval_append,hpbad]
      rfl
    have hw := word_outcome hstep n mid
    rw [hwbad] at hw
    exact halts_of_prefix hm hw

theorem nonhalting_implies_arithmeticSafe
    (hno : ¬ CycleHalts exactSites (commandConfig 0 0 0 0 commandInitial)) :
    Scheduler.ArithmeticSafe := by
  intro n p rest hp hbad
  exact hno (prefix_halts hstep n p rest hp hbad)

#print axioms word_outcome
#print axioms prefix_halts
#print axioms nonhalting_implies_arithmeticSafe
end M6.Source.CommandRunTransfer

