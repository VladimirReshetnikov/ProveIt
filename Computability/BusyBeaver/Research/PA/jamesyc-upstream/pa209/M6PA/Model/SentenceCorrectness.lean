module
public import M6PA.Model.EndpointTraceAdequacy
public import M6PA.Model.EndpointPhysicalAdequacy
@[expose] public section
namespace M6.Arithmetic.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
/-- The auxiliary arithmetic formula has exactly the same blank-halting
meaning as the209-working-state partial physical table. -/
theorem sentence_iff_physical_nonhalting :
    (Nat ⊧/![] HaltingFormula.nonhaltingSentence) ↔
      ¬ M6.Zip.Halts M6.Table.machine (M6.Conjugacy.mapConf M6.Startup.blank) := by
  rw [HaltingFormula.nonhaltingSentence_iff, ← NatTape.blank_halts_iff]
  exact not_congr PhysicalAdequacy.blank_halts_iff.symm
#print axioms sentence_iff_physical_nonhalting
end M6.Arithmetic.PA
