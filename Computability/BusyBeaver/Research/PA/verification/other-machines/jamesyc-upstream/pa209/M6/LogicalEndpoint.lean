module
public import M6.Source.CommandTransfer
public import M6.Source.CyclicInvariant
public import M6.ZeroStackSafety
public import M6.Legacy211.SourceEquivalence
public import M6.PhysicalEndpoint
@[expose] public section
namespace M6.LogicalEndpoint
open M6.Source M6.Source.Enumeration M6.ZeroStackSafety
open M6.PA.NativeCalculus

def SoundBoundary (c : Configuration) : Prop :=
  ∃ n l s, c = commandConfig 0 n l 0 s ∧ SoundStore s

/-- Every source command boundary with a sound zero-tail stack has a positive
finite next macro execution. The arbitrary N/L fields are retained exactly. -/
theorem progress (hn : ¬ Proved 1) (c : Configuration) (hc : SoundBoundary c) :
    ∃ m d, 0 < m ∧ CycleSteps exactSites m c d ∧ SoundBoundary d := by
  obtain ⟨n,l,s,rfl,hs⟩ := hc
  obtain ⟨out,he,ho⟩ := command_safe hn (parse (FetchDispatch.seed n l)).command s hs
  obtain ⟨m,hm,hsteps⟩ := parsed_command_step n l s out he
  exact ⟨m,_,hm,hsteps,_,_,out,rfl,ho⟩

theorem source_nonhalting (hn : ¬ Proved 1) (n l : Nat) (s : CommandStore)
    (hs : SoundStore s) : ¬ CycleHalts exactSites (commandConfig 0 n l 0 s) := by
  apply cycle_not_halts_of_positive_invariant exactSites SoundBoundary
  · rintro c ⟨n,l,s,rfl,_⟩
    simp [commandConfig]
  · exact progress hn
  · exact ⟨n,l,s,rfl,hs⟩

theorem seed_eq :
    (⟨.at 0,readFile Startup.physicalFile⟩ : Configuration) =
      commandConfig 0 2 0 0 zeroStore := by
  apply congrArg (Configuration.mk (.at 0))
  funext r
  exact (by decide +kernel : ∀ r : Fin 9,
    readFile Startup.physicalFile r = commandRegisters 2 0 0 zeroStore r) r

theorem original_source_nonhalting (hn : ¬ Proved 1) :
    ¬ CycleHalts SourceCrosswalk.originalSites
      ⟨.at 0,readFile Startup.physicalFile⟩ := by
  change ¬ CycleHalts Legacy211.Source.sites ⟨.at 0,readFile Startup.physicalFile⟩
  rw [Legacy211.Source.cycleHalts_iff,seed_eq]
  exact source_nonhalting hn 2 0 zeroStore zero_sound

/-- Full natural physical/source theorem with one explicit mathematical
premise: non-refutation of the finite native calculus. The separate PA
module discharges precisely that premise from ordinary PA consistency. -/
theorem blank_nonhalting (hn : ¬ Proved 1) :
    ¬ Zip.Halts Literal.machine Startup.blank :=
  PhysicalEndpoint.blank_nonhalting_of_original_source (original_source_nonhalting hn)

#print axioms source_nonhalting
#print axioms seed_eq
#print axioms original_source_nonhalting
#print axioms blank_nonhalting
end M6.LogicalEndpoint
