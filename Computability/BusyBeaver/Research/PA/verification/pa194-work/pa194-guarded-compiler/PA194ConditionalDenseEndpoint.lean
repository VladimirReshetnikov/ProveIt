import PA194ConditionalNativeForward
import PA194ModeledHaltRefutesPA

/-! Assemble both object-theory implications with the physical obligations explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PA194ConditionalDenseEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula
open ConPA.ISigma1Models PA194FullSepIPRA PA194ConditionalNativeForward
open LO.FirstOrder.Arithmetic.Bootstrapping

/-- Literal-machine halting reaches an encoded scheduler halt in each covered model. -/
def PhysicalToScheduler : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA], ReductISigma1 M →
      (M↓[language] ⊧ PA194ExplicitEndpoint.haltClassical) → schedulerHalt M

/-- The consistency-to-nonhalting direction uses only the physical-to-scheduler bridge. -/
theorem consistency_implies_physical_nonhalt (hsync : PhysicalToScheduler) :
    standardTheory ⊢ nativePAConsistency 🡒 ∼PA194ExplicitEndpoint.haltSentence := by
  apply ConPA.Directions.ipra_consistency_implies_nonhalt PA194ExplicitEndpoint.haltMatrix
  · simp [PA194ExplicitEndpoint.haltMatrix, Semiformula.Open]
  · intro M _ _ _ _ hr hhalt
    obtain ⟨t, ht⟩ := hsync M hr hhalt
    letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
    letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
    letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
    letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
    letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
    rw [models_iff, PA195RefutationBridge.mapped_refutation_iff]
    exact PA194ModeledHaltRefutesPA.modeled_halt_refutes_PA t ht

/-- Both directions use the same literal-machine halting sentence. -/
theorem consistency_iff_physical_nonhalt (harith : ArithmeticCalibration)
    (forward : SchedulerToPhysical) (reverse : PhysicalToScheduler) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA194ExplicitEndpoint.haltSentence := by
  obtain ⟨hp⟩ := consistency_implies_physical_nonhalt reverse
  obtain ⟨hq⟩ := physical_nonhalt_implies_consistency harith forward
  exact ⟨Entailment.K_intro hp hq⟩

#print axioms consistency_implies_physical_nonhalt
#print axioms consistency_iff_physical_nonhalt
end PA194ConditionalDenseEndpoint
