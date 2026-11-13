module
public import M6.Source.SourceSemanticEquivalence
@[expose] public section
namespace M6.Source
open Enumeration

/-- The literal enumeration reaches every universally halting finite command
word, unless an earlier schedule prefix has already halted. -/
theorem universal_commands_not_safe (cs : List Command)
    (huniversal : ∀ s, commandsEval cs s = none) : ¬ Scheduler.ArithmeticSafe := by
  intro hsafe
  cases cs with
  | nil =>
      have hh := huniversal commandInitial
      simp [commandsEval] at hh
  | cons c cs =>
      let n := encodeWord (c::cs) 0 - 1
      have hw : word n = (c::cs)++[] := by
        simpa only [n,residual,List.append_nil] using word_candidate c cs 0
      apply hsafe n (c::cs) [] hw
      rw [commandsEval_append]
      cases commandsEval (schedule n) commandInitial with
      | none => rfl
      | some s => exact huniversal s

/-- Concrete source halting follows from an actual universally halting word;
there is no assumed command enumeration or source simulation supplier. -/
theorem universal_commands_intermediate_halts (cs : List Command)
    (huniversal : ∀ s, commandsEval cs s = none) :
    CycleHalts exactSites SeedPrefix.intermediate :=
  intermediate_halts_iff_not_arithmeticSafe.mpr (universal_commands_not_safe cs huniversal)

#print axioms universal_commands_not_safe
#print axioms universal_commands_intermediate_halts
end M6.Source

