import PA194SourcePositiveDecoderRound
import PA194SourceSite36PositiveReturn
import PA194SourceSite34PositivePhysical
import PA194Site35ClockExists
import PA194SourceSite35Controller
import PA194Site36PositiveClockExists
import PA194SourceSite37Physical
import PA194SourceSite41Physical
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourcePositiveDecoderSingle
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194SourceControllerCode PA194SourceSite31Controller PA194SourceSite31Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem positiveSingle (k count tail m6 m8 : M) (args : Fin 11 → M)
    (h6 : args 6 = m6+1) (h8 : args 8 = m8+1)
    (he : PA194RegisterPermutation.physicalArgs args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let a := Function.update args 8 m8
    let b := PA194Site35OutputFile.updated a count
    let out := Function.update b 6 m6
    ∃ c : M,
      F step ![F step ![F step ![F step ![F step ![sourceState 34 args tail]]]]] = sourceState 34 out tail ∧
      F PA194Stepper.stepper ![c,physicalFrame 34 (((((k+1)+1)+1)+1)+1) args] =
        physicalFrame 34 (((((((k+1)+1)+1)+1)+1)+1)+1) out := by
  obtain ⟨c34,c35,c36,hc,hp⟩ := PA194SourcePositiveDecoderRound.positiveRound k count tail m6 m8 args h6 h8 he
  refine ⟨F addCode ![F addCode ![c34,c35],c36],hc,?_⟩
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hp]
#print axioms positiveSingle
end models
end PA194SourcePositiveDecoderSingle
