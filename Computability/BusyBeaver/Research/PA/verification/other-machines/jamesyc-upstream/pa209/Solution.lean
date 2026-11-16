module
public import PATheoryBridge
public import M6RowsBridge
public import TraceBridge
public import NthBridge
public import M6PA.TwoSidedIndependence
public import PhysicalBridge
@[expose] public section
/-! The exact PA sentences and tape semantics agree with the PA209 development. -/
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

theorem m6Halting_toFoundation : m6Halting.toFoundation =
    M6.Arithmetic.PA.ExactHaltingFormula.traceSentence := by
  rw [m6Halting,traceFormula_exact nthFormula_toFoundation,m6Step_exact]
  rfl

theorem m6Nonhalting_toFoundation : m6Nonhalting.toFoundation =
    M6.Arithmetic.PA.ExactHaltingFormula.nonhaltingSentence := by
  rw [m6Nonhalting,Formula.to_neg,m6Halting_toFoundation]
  rfl

/-- Ordinary PA cannot prove either exact-M6 halting or nonhalting. -/
theorem m6_two_sided_independence :
    (¬ Provable PATheory m6Nonhalting) ∧ (¬ Provable PATheory m6Halting) := by
  constructor
  · intro h
    have hp := (pa_provable_iff m6Nonhalting).mp h
    rw [m6Nonhalting_toFoundation] at hp
    exact M6.Arithmetic.PA.Independence.two_sided_independence.1 hp
  · intro h
    have hp := (pa_provable_iff m6Halting).mp h
    rw [m6Halting_toFoundation] at hp
    exact M6.Arithmetic.PA.Independence.halting_unprovable hp
/-- The literal binary machine runs forever from a blank tape. -/
theorem m6_machine_nonhalting : ¬ ∃ n c, machineRun n blank = some c ∧ machineStep c = none := by
  rintro ⟨n, c, hr, hs⟩
  apply M6.Arithmetic.PA.Independence.machine_nonhalting
  refine ⟨c.toZip, ⟨n, ?_⟩, ?_⟩
  · have hb : blank.toZip = M6.Startup.blank := rfl
    simpa only [hr, Option.map_some, hb] using (machineRun_eq n blank).symm
  · simpa only [hs, Option.map_none] using (machineStep_eq c).symm
end PalomarPA
