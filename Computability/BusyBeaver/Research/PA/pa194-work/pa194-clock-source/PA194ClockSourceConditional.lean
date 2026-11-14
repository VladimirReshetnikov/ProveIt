import PA194SeedBridge
import PA194DenseGlobal
import PA194ZipRun
import PA194ParentZip
import PackedStandard

/-! Standard-model composition with coverage and startup still explicit. -/
set_option autoImplicit false
namespace PA194ClockSourceConditional
open M6.Source PA194LocalQuotient PA194SeedBridge PA194SourceProgram
open PA194ZipBridge PA194ParentZip
open DiophantineConsistency.PRAFiniteFunctionCodes
open List.Vector

theorem parent_blank_related :
    Related (⟨74, 0, fun _ => false⟩ : PA194LocalQuotient.Configuration) blank := by
  refine ⟨rfl, ?_⟩
  intro i
  cases i <;> rfl

theorem parent_blank_full_iff_zip :
    PA195GenericTrace.Halts (fullStep parent) AtHalt ⟨74, 0, fun _ => false⟩ ↔
      M6.Zip.Halts PA194RuntimeEngine.machine blank := by
  have hv : validControl (⟨74, 0, fun _ => false⟩ : PA194LocalQuotient.Configuration).state :=
    start_valid (fun _ => false) 0
  exact parent_halts_iff_zip _ _ parent_blank_related hv

/-- Standard meaning of the selected clock, conditional on exact coverage and
startup reachability. This is not a PRA or iPRA theorem. -/
theorem clock_iff_source
    (hcoverage : PA194CompilerCorrectness.Coverage sites path 3673)
    (hstartup : M6.Zip.Reach PA194RuntimeEngine.machine blank seedFrame) :
    (∃ n, eval PA194Bounded.boundedCode (n ::ᵥ nil) = 1) ↔
      CycleHalts sites ⟨.at 25, readFile seedFile⟩ := by
  calc
    (∃ n, eval PA194Bounded.boundedCode (n ::ᵥ nil) = 1) ↔
        PA195GenericTrace.Halts (fullStep dense) (fun c => c.state = 194) blankFull :=
          bounded_code_iff_full
    _ ↔ PA195GenericTrace.Halts (fullStep parent) AtHalt ⟨74, 0, fun _ => false⟩ := by
      exact (parent_dense_halts 0 (fun _ => false)).symm
    _ ↔ M6.Zip.Halts PA194RuntimeEngine.machine blank := parent_blank_full_iff_zip
    _ ↔ CycleHalts sites ⟨.at 25, readFile seedFile⟩ :=
      parent_blank_iff_source hcoverage hstartup

/-- Both fixed clock codes have the same value at each standard natural. -/
theorem explicit_clock_agrees (n : Nat) :
    eval PackedClock.haltIndicator (n ::ᵥ nil) =
      eval PA194Bounded.boundedCode (n ::ᵥ nil) := by
  rw [PackedStandard.evalHaltIndicator, PA194Bounded.boundedCode_eval]

/-- The explicit primitive-recursive clock has the same conditional source
meaning, in the standard naturals. -/
theorem explicit_clock_iff_source
    (hcoverage : PA194CompilerCorrectness.Coverage sites path 3673)
    (hstartup : M6.Zip.Reach PA194RuntimeEngine.machine blank seedFrame) :
    (∃ n, eval PackedClock.haltIndicator (n ::ᵥ nil) = 1) ↔
      CycleHalts sites ⟨.at 25, readFile seedFile⟩ := by
  have h : (∃ n, eval PackedClock.haltIndicator (n ::ᵥ nil) = 1) ↔
      (∃ n, eval PA194Bounded.boundedCode (n ::ᵥ nil) = 1) := by
    constructor <;> rintro ⟨n, hn⟩
    · exact ⟨n, (explicit_clock_agrees n).symm.trans hn⟩
    · exact ⟨n, (explicit_clock_agrees n).trans hn⟩
  exact h.trans (clock_iff_source hcoverage hstartup)

#print axioms explicit_clock_agrees
#print axioms explicit_clock_iff_source
#print axioms parent_blank_full_iff_zip
#print axioms clock_iff_source
end PA194ClockSourceConditional
