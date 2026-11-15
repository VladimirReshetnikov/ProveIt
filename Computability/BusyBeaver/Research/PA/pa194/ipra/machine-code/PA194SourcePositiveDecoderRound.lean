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
namespace PA194SourcePositiveDecoderRound
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

theorem positiveRound (k count tail m6 m8 : M) (args : Fin 11 → M)
    (h6 : args 6 = m6+1) (h8 : args 8 = m8+1)
    (he : PA194RegisterPermutation.physicalArgs args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let a := Function.update args 8 m8
    let b := PA194Site35OutputFile.updated a count
    let out := Function.update b 6 m6
    ∃ c34 c35 c36 : M,
      F step ![F step ![F step ![F step ![F step ![sourceState 34 args tail]]]]] = sourceState 34 out tail ∧
      F PA194Stepper.stepper ![c36,F PA194Stepper.stepper ![c35,F PA194Stepper.stepper ![c34,
        physicalFrame 34 (((((k+1)+1)+1)+1)+1) args]]] =
        physicalFrame 34 (((((((k+1)+1)+1)+1)+1)+1)+1) out := by
  dsimp only
  let a := Function.update args 8 m8
  let b := PA194Site35OutputFile.updated a count
  let out := Function.update b 6 m6
  have hea : PA194RegisterPermutation.physicalArgs a 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)] := by
    change Function.update args 8 m8 10 = _
    rw [Function.update_of_ne (by decide)]
    exact he
  have hb6 : b 6 = m6+1 := by
    dsimp only [b,PA194Site35OutputFile.updated,a]
    simp [h6]
  have h34 := PA194SourceSite34PositivePhysical.positiveBranch (((k+1)+1)+1) tail m8 args h8
  have hc35 := PA194SourceSite35Controller.controllerStep a tail (F PA194OneSpareReturn.repeatOutput ![F Code.succ (fun _ => count),(0 : M)])
  change F step ![sourceState 35 a tail] = sourceState 36 b tail at hc35
  obtain ⟨c35,h35⟩ := PA194Site35ClockExists.existsClock ((k+1)+1) count a hea
  obtain ⟨c36,hc36,h36⟩ := PA194SourceSite36PositiveReturn.positiveReturn k tail m6 b hb6
  refine ⟨F addCode ![PA194Site34PositiveTo16.clock (((k+1)+1)+1) args,modelNumeral M 23],c35,c36,?_,?_⟩
  · rw [h34.1,hc35,hc36]
  · rw [h34.2,h35,h36]
#print axioms positiveRound
end models
end PA194SourcePositiveDecoderRound
