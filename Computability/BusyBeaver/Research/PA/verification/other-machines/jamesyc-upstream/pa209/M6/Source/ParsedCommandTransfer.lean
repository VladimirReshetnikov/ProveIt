module
public import M6.Source.CommandAXRegisters
@[expose] public section
namespace M6.Source
open Cantor Enumeration

/-- Exact fetch, parser, operand consumption and actual macro execution compose
into one positive source command segment. All three commands use actual rows. -/
theorem parsed_command_step_of_ax
    (hax : ∀ (n tail c x y : Nat) (s out : CommandStore),
      commandEval (.ax c x y) s = some out →
      ∃ m, 0 < m ∧ CycleSteps exactSites m
        (commandConfig 25 n (pair y (pair x tail)) c s) (commandConfig 0 n tail 0 out))
    (n l : Nat) (s out : CommandStore)
    (he : commandEval (parse (FetchDispatch.seed n l)).command s = some out) :
    ∃ m, 0 < m ∧ CycleSteps exactSites m (commandConfig 0 n l 0 s)
      (commandConfig 0 (FetchDispatch.nextN n l) (parse (FetchDispatch.seed n l)).next 0 out) := by
  obtain ⟨nf,hf,sf⟩ := fetch_command n l s
  cases hk : (decode (FetchDispatch.seed n l)).1 with
  | zero =>
    have he' : commandEval .shift s = some out := by simpa only [parse,hk] using he
    obtain ⟨ns,hs,ss⟩ := shift_command (FetchDispatch.nextN n l)
      (decode (FetchDispatch.seed n l)).2 s out he'
    have sf' : CycleSteps exactSites nf (commandConfig 0 n l 0 s)
        (commandConfig 3911 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 s) := by
      simpa [parsedEntry,hk,Dispatch.target] using sf
    exact ⟨nf+ns,by omega,by simpa only [parse,hk] using sf'.append ss⟩
  | succ k =>
    cases k with
    | zero =>
      have he' : commandEval (.mp (decode (decode (FetchDispatch.seed n l)).2).1) s = some out := by
        simpa only [parse,hk] using he
      obtain ⟨ns,hs,ss⟩ := mp_command (FetchDispatch.nextN n l)
        (decode (decode (FetchDispatch.seed n l)).2).2
        (decode (decode (FetchDispatch.seed n l)).2).1 s out he'
      rw [pair_decode] at ss
      have sf' : CycleSteps exactSites nf (commandConfig 0 n l 0 s)
          (commandConfig 3804 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 0 s) := by
        simpa [parsedEntry,hk,Dispatch.target] using sf
      exact ⟨nf+ns,by omega,by simpa only [parse,hk] using sf'.append ss⟩
    | succ c =>
      have he' : commandEval (.ax c
          (decode (decode (decode (FetchDispatch.seed n l)).2).2).1
          (decode (decode (FetchDispatch.seed n l)).2).1) s = some out := by
        simpa only [parse,hk] using he
      obtain ⟨ns,hs,ss⟩ := hax (FetchDispatch.nextN n l)
        (decode (decode (decode (FetchDispatch.seed n l)).2).2).2 c
        (decode (decode (decode (FetchDispatch.seed n l)).2).2).1
        (decode (decode (FetchDispatch.seed n l)).2).1 s out he'
      rw [pair_decode,pair_decode] at ss
      have sf' : CycleSteps exactSites nf (commandConfig 0 n l 0 s)
          (commandConfig 25 (FetchDispatch.nextN n l) (decode (FetchDispatch.seed n l)).2 c s) := by
        simpa [parsedEntry,hk,Dispatch.target,Nat.add_assoc] using sf
      exact ⟨nf+ns,by omega,by simpa only [parse,hk] using sf'.append ss⟩
#print axioms parsed_command_step_of_ax
end M6.Source

