import PA194LiteralSchedulerCorrectness
import PA194NativeCalibratedEndpoint
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194NativeLiteralFinal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula ConPA.ISigma1Models
open PA194FullSepIPRA PA194NativeCalibratedEndpoint

theorem physicalSchedulerEquiv : PhysicalSchedulerEquiv := by
  intro M _ _ _ _ hr
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  simpa only [schedulerHalt, PA194SchedulerHaltCode.haltAfter_model,
    show (1 : M) = Structure.func (L := language) oneCode Fin.elim0 from rfl] using
    (PA194LiteralSchedulerCorrectness.endpoint (M := M))

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA194ExplicitEndpoint.haltSentence :=
  PA194NativeCalibratedEndpoint.physical_iff_consistency physicalSchedulerEquiv
#print axioms physicalSchedulerEquiv
#print axioms consistency_iff_literal_nonhalt
end PA194NativeLiteralFinal
