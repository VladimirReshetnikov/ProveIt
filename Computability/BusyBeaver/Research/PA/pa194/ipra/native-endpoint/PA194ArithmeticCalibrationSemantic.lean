import PA194ConditionalNativeForward
import PA194SourceArithmetic
import PA194SourceMulCoherence
import PA194SourceAddComm
import PA194FullSourceRefutationReduction
import PA194MulTotalGuardedModel
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194ArithmeticCalibrationSemantic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula ConPA.ISigma1Models PA194ConditionalNativeForward

theorem arithmeticCalibration : ArithmeticCalibration := by
  intro M _ _ _ _ hr
  letI : Zero M := ⟨Structure.func (L := PRALanguage.language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := PRALanguage.language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := PRALanguage.language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := PRALanguage.language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  letI := adjunctiveFullSepTheoryDelta
  exact PA194SourceModel.calibration

#print axioms arithmeticCalibration
end PA194ArithmeticCalibrationSemantic
