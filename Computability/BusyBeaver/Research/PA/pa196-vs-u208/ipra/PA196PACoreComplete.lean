import PA196PAIdentityBounds
import PA196PASimpleRuleBounds
import PA196PAAllBounds
import PA196PAExistentialRuleBounds
import PA196PAShiftRuleBounds
import PA196PACutBounds
import PA196InductionRecognizerComplete
import PA196PAFormulaSetComplete

/-! Complete candidate-PRA witness bounds for both exact Foundation PA
derivation-core polarities. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace PA196PACoreComplete
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_core_sigma : WB M (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  change WB M (PA196PAFormulaSetBound.actualSigmaLeft ⋏
    (PA196PAIdentityBounds.actualPositive ⋎ PA196PASimpleRuleBounds.positiveVerum ⋎
      PA196PASimpleRuleBounds.positiveAnd ⋎ PA196PASimpleRuleBounds.positiveOr ⋎
      PA196PAAllBounds.actualPositive ⋎ PA196PAExistentialRuleBounds.actualPositive ⋎
      PA196PASimpleRuleBounds.positiveWeakening ⋎ PA196PAShiftRuleBounds.actualPositive ⋎
      PA196PACutBounds.actualPositive ⋎ PA196PAAxiomBound.actualPositive))
  exact wb_and PA196PAFormulaSetComplete.wb_actualSigmaLeft
    (wb_or PA196PAIdentityBounds.wb_positiveIdentity
    (wb_or PA196PASimpleRuleBounds.wb_positiveVerum
    (wb_or PA196PASimpleRuleBounds.wb_positiveAnd
    (wb_or PA196PASimpleRuleBounds.wb_positiveOr
    (wb_or PA196PAAllBounds.wb_positiveAll
    (wb_or PA196PAExistentialRuleBounds.wb_positive
    (wb_or PA196PASimpleRuleBounds.wb_positiveWeakening
    (wb_or PA196PAShiftRuleBounds.wb_positive
    (wb_or PA196PACutBounds.wb_positiveCut PA196InductionRecognizerComplete.axiom_branches.1)))))))))

theorem wb_core_neg_pi : WB M (∼(Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  change WB M (∼(PA196PAFormulaSetBound.actualPiLeft ⋏
    (PA196PAIdentityBounds.actualNegative ⋎ PA196PASimpleRuleBounds.negativeVerum ⋎
      PA196PASimpleRuleBounds.negativeAnd ⋎ PA196PASimpleRuleBounds.negativeOr ⋎
      PA196PAAllBounds.actualNegative ⋎ PA196PAExistentialRuleBounds.actualNegative ⋎
      PA196PASimpleRuleBounds.negativeWeakening ⋎ PA196PAShiftRuleBounds.actualNegative ⋎
      PA196PACutBounds.actualNegative ⋎ PA196PAAxiomBound.actualNegative)))
  simpa only [DeMorgan.and, DeMorgan.or] using
    wb_or PA196PAFormulaSetComplete.wb_neg_actualPiLeft
    (wb_and PA196PAIdentityBounds.wb_negativeIdentity
    (wb_and PA196PASimpleRuleBounds.wb_negativeVerum
    (wb_and PA196PASimpleRuleBounds.wb_negativeAnd
    (wb_and PA196PASimpleRuleBounds.wb_negativeOr
    (wb_and PA196PAAllBounds.wb_negativeAll
    (wb_and PA196PAExistentialRuleBounds.wb_negative
    (wb_and PA196PASimpleRuleBounds.wb_negativeWeakening
    (wb_and PA196PAShiftRuleBounds.wb_negative
    (wb_and PA196PACutBounds.wb_negativeCut PA196InductionRecognizerComplete.axiom_branches.2)))))))))

#print axioms wb_core_sigma
#print axioms wb_core_neg_pi
end PA196PACoreComplete
