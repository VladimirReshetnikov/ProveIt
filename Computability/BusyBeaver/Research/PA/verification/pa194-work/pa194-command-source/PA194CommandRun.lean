import PA194FetchCommand
set_option autoImplicit false
set_option maxRecDepth 100000
namespace PA194CommandRun
open M6.Source M6.Source.Cantor PA196 PA194CommandRegisters PA194FetchCommand PA194FetchSource

structure State where
  n : Nat
  l : Nat
  store : Commands.Store

def config (s : State) : Configuration := commandConfig 25 s.n s.l 0 s.store

def advance (s : State) : Option State :=
  match PA194CommandTransfer.step (parse (FetchDispatch.seed s.n s.l)).command s.store with
  | none => none
  | some out => some ⟨FetchDispatch.nextN s.n s.l, (parse (FetchDispatch.seed s.n s.l)).next, out⟩

def run : Nat → State → Option State
  | 0,s => some s
  | k+1,s => (advance s).bind (run k)

theorem advance_sound {s s' : State} (h : advance s = some s') :
    ∃ n, 0<n ∧ CycleSteps PA194SourceProgram.sites n (config s) (config s') := by
  cases hs : PA194CommandTransfer.step (parse (FetchDispatch.seed s.n s.l)).command s.store with
  | none => simp [advance,hs] at h
  | some out =>
    simp only [advance,hs,Option.some.injEq] at h
    subst s'
    exact parsed_command_step s.n s.l s.store out hs

theorem run_sound (k : Nat) {s s' : State} (h : run k s = some s') :
    ∃ n, CycleSteps PA194SourceProgram.sites n (config s) (config s') := by
  induction k generalizing s with
  | zero =>
    simp only [run,Option.some.injEq] at h
    subst s'
    exact ⟨0,CycleSteps.refl _⟩
  | succ k ih =>
    cases ha : advance s with
    | none => simp [run,ha] at h
    | some mid =>
      simp only [run,ha,Option.bind_some] at h
      obtain ⟨n,_,hn⟩ := advance_sound ha
      obtain ⟨m,hm⟩ := ih h
      exact ⟨n+m,hn.append hm⟩

theorem advance_halts_source {s : State} (h : advance s = none) :
    CycleHalts PA194SourceProgram.sites (config s) := by
  cases hs : PA194CommandTransfer.step (parse (FetchDispatch.seed s.n s.l)).command s.store with
  | none =>
    obtain ⟨n,_,hn⟩ := parsed_command_halts s.n s.l s.store hs
    refine ⟨n, ?_⟩
    change (cycleRun PA194SourceProgram.sites n (commandConfig 25 s.n s.l 0 s.store)).control = .halted
    rw [hn.eq_run]
  | some out => simp [advance,hs] at h

theorem scheduler_halts_source {s s' : State} (k : Nat)
    (h : run k s = some s') (hh : advance s' = none) :
    CycleHalts PA194SourceProgram.sites (config s) := by
  obtain ⟨n,hn⟩ := run_sound k h
  obtain ⟨m,hm⟩ := advance_halts_source hh
  exact ⟨n+m, by rw [cycleRun_add,hn.eq_run]; exact hm⟩

#print axioms run_sound
#print axioms scheduler_halts_source
end PA194CommandRun
