module
public import PA196.Source.CommandTransfer
public import PA196.Logic.CommandSoundness
@[expose] public section
namespace PA196.Source
open M6.Source Logic.CommandSoundness

/-- A command boundary with two proved live formulas and a proved stack. -/
def SoundBoundary (c : Configuration) : Prop :=
  ∃ n l s, c = commandConfig 25 n l 0 s ∧ SoundStore s

private theorem boundary_not_halted (c : Configuration) (hc : SoundBoundary c) :
    c.control ≠ .halted := by
  obtain ⟨n,l,s,rfl,_⟩ := hc
  simp [commandConfig]

private theorem boundary_progress (c : Configuration) (hc : SoundBoundary c) :
    ∃ n d, 0<n ∧ CycleSteps Program.sites n c d ∧ SoundBoundary d := by
  obtain ⟨n,l,s,rfl,hs⟩ := hc
  obtain ⟨out,he,ho⟩ := command_safe (parse (FetchDispatch.seed n l)).command s hs
  obtain ⟨m,hm,hstep⟩ := parsed_command_step n l s out he
  exact ⟨m,_,hm,hstep,FetchDispatch.nextN n l,(parse (FetchDispatch.seed n l)).next,out,rfl,ho⟩

/-- Unconditional nonhalting from every sound command boundary. The concrete
HF model discharges soundness; the macro interpreter is bound to PA196 rows. -/
theorem sound_nonhalting (n l : Nat) (s : Commands.Store) (hs : SoundStore s) :
    ¬ CycleHalts Program.sites (commandConfig 25 n l 0 s) :=
  cycle_not_halts_of_positive_invariant Program.sites SoundBoundary
    boundary_not_halted boundary_progress _ ⟨n,l,s,rfl,hs⟩

/-- The decoded register state at the end of the literal blank-tape startup. -/
def initial : Configuration := commandConfig 25 2 0 0 zeroStore

theorem initial_nonhalting : ¬ CycleHalts Program.sites initial :=
  sound_nonhalting 2 0 zeroStore zero_sound

#print axioms sound_nonhalting
#print axioms initial_nonhalting
end PA196.Source
