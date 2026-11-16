import PA194FullSourceRefutationReduction
import PA194FullSepIPRA
import PA194SourceFactsTen
import PA194PAeqFiniteSupplier
import PA195RefutationBridge

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace PA194ConditionalNativeForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula ConPA.ISigma1Models
open PA194ModelLogic PA194BindSource PA194GuardedCompiler PA194Schematic PA194FullSepIPRA

/-- Availability of the four remaining source proofs in each covered model. -/
def ArithmeticCalibration : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] (hr : ReductISigma1 M),
    letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
    letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
    letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
    letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
    letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
    letI := adjunctiveFullSepTheoryDelta
    ((adjunctiveFullSepTheory.internalize M) ⊢ tHyp sA2) ∧
    ((adjunctiveFullSepTheory.internalize M) ⊢ tHyp sM2) ∧
    ((adjunctiveFullSepTheory.internalize M) ⊢ tHyp sA3) ∧
    ((adjunctiveFullSepTheory.internalize M) ⊢ tHyp sM3)

/-- Supply the exact source calibration consumed by the native endpoint. -/
theorem source_calibration (h : ArithmeticCalibration) : SourceCalibration := by
  intro M _ _ _ _ hr hp
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  letI := adjunctiveFullSepTheoryDelta
  letI := PA194PAeqBind.ordinaryPAeq_delta
  obtain ⟨ha2, hm2, ha3, hm3⟩ := h M hr
  have hpa : Provable (𝗣𝗔 : ArithmeticTheory) (qqFalsum : M) := by
    rw [models_iff, PA195RefutationBridge.mapped_refutation_iff] at hp
    obtain ⟨d, hd⟩ := hp
    exact ⟨d, by simpa [Sentence.quote_def] using hd⟩
  obtain ⟨d, hd⟩ := PA194PAeq.InductionReopen.pa_refutation_to_ordinary hpa
  exact PA194FullSourceRefutationReduction.refutation_of_source_facts
    (PA194SourceFactsTen.sourceFacts_of_two ha2 hm2) ha3 hm3 hd

/-- Conditional native iPRA direction for the modeled scheduler. -/
theorem scheduler_nonhalt_implies_consistency (h : ArithmeticCalibration) :
    standardTheory ⊢ ∼modeledHaltSentence 🡒 nativePAConsistency :=
  modeled_nonhalt_implies_PA_consistency (source_calibration h)

/-- Conditional native iPRA direction for the pinned machine. -/
theorem physical_nonhalt_implies_consistency (h : ArithmeticCalibration) (hsync : SchedulerToPhysical) :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡒 nativePAConsistency :=
  physical_nonhalt_implies_PA_consistency (source_calibration h) hsync

#print axioms source_calibration
#print axioms scheduler_nonhalt_implies_consistency
#print axioms physical_nonhalt_implies_consistency
end PA194ConditionalNativeForward
