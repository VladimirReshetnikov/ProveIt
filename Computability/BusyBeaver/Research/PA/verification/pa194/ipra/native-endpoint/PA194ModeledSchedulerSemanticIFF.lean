import PA194SourceArithmetic
import PA194PARefutationScheduler
import PA194ModeledHaltRefutesPA
import PA194SourceMulCoherence
import PA194SourceAddComm
import PA194FullSourceRefutationReduction
import PA194MulTotalGuardedModel
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194ModeledSchedulerSemanticIFF
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance calibratedSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance calibratedSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance calibratedSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance calibratedSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance calibratedSourceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance calibratedSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194GuardedCompiler PA194Schematic

attribute [local instance] adjunctiveFullSepTheoryDelta

open PA194SchedulerHaltCode

theorem scheduler_iff_pa_refutation :
    (∃ k : M, F haltAfter ![k] = 1) ↔ Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) := by
  constructor
  · rintro ⟨k, hk⟩
    exact PA194ModeledHaltRefutesPA.modeled_halt_refutes_PA k hk
  · intro hp
    obtain ⟨_, _, ha3, hm3⟩ := PA194SourceModel.calibration (V := M)
    exact PA194PARefutationScheduler.scheduler_halts_of_pa_refutation
      PA194SourceModel.sourceFacts_semantic ha3 hm3 hp
#print axioms scheduler_iff_pa_refutation
end models

end PA194ModeledSchedulerSemanticIFF
