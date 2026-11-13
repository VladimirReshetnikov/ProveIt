module
public import PA196.PhysicalEndpoint
public import PA196.Source.Nonhalting
@[expose] public section

/-! Unconditional nonhalting of the exact supplied 196-state binary table.
The arithmetic unprovability theorem is a separate result; it does not follow
merely from this external soundness and machine simulation theorem. -/
namespace PA196

private theorem startup_source_initial :
    (⟨.at 25,M6.Source.readFile Startup.physicalFile⟩ : M6.Source.Configuration) =
      Source.initial := by
  apply congrArg (M6.Source.Configuration.mk (.at 25))
  funext r
  exact (by decide : ∀ r : Fin 9,
    M6.Source.readFile Startup.physicalFile r =
      Source.commandRegisters 2 0 0 Logic.CommandSoundness.zeroStore r) r

/-- The table in `data/pa196.tm`, started at state 0 on a blank tape,
never reaches an undefined transition. No consistency assumption is used. -/
theorem machine_nonhalting : ¬ M6.Zip.Halts Literal.machine Startup.blank := by
  apply PhysicalEndpoint.blank_nonhalting_of_source
  rw [startup_source_initial]
  exact Source.initial_nonhalting

#print axioms machine_nonhalting
end PA196
