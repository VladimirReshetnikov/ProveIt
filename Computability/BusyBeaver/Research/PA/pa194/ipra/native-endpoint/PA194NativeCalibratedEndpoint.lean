import PA194ArithmeticCalibrationSemantic
import PA194ConditionalDenseEndpoint
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194NativeCalibratedEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula ConPA.ISigma1Models
open PA194FullSepIPRA PA194ConditionalDenseEndpoint

def PhysicalSchedulerEquiv : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA], ReductISigma1 M →
      ((M↓[language] ⊧ PA194ExplicitEndpoint.haltClassical) ↔ schedulerHalt M)

theorem scheduler_nonhalt_implies_consistency :
    standardTheory ⊢ ∼modeledHaltSentence 🡒 nativePAConsistency :=
  PA194ConditionalNativeForward.scheduler_nonhalt_implies_consistency
    PA194ArithmeticCalibrationSemantic.arithmeticCalibration

theorem physical_iff_consistency (h : PhysicalSchedulerEquiv) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA194ExplicitEndpoint.haltSentence := by
  apply PA194ConditionalDenseEndpoint.consistency_iff_physical_nonhalt
    PA194ArithmeticCalibrationSemantic.arithmeticCalibration
  · intro M _ _ _ _ hr hs
    exact (h M hr).mpr hs
  · intro M _ _ _ _ hr hs
    exact (h M hr).mp hs
#print axioms scheduler_nonhalt_implies_consistency
#print axioms physical_iff_consistency
end PA194NativeCalibratedEndpoint
