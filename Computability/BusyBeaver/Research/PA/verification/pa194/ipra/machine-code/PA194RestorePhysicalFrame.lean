import PA194ActualLoopOrbit
import PA194ActualRestoreSource
import PA194ModelLoopFrameAt
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace PA194RestorePhysicalFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopState PA194ModelLoopFrame PA194ControllerLoopFrame PA194OneSpareReturn PA194ZeroRuns PA194StateOne PA194UnaryRuns PA194BinaryDouble PA194FiniteControls PA194RegisterFile PA194RegisterPermutation PA194Path27Header BinaryTapeCodes PackedDecoderModel TableDispatch
open PA194SourceControllerCode PA194SourceRegisters PA194SourceRegisterRelation PA194SourceInstructionModel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem readSource (r : Fin 9 → M) (tail : M) (i : Fin 9) :
    F (readers i) (fun _ => PA194ModelRestoreSource.source r tail) = r i := by
  have hv : (![PA194ModelRestoreSource.source r tail] : Fin 1 → M) = fun _ => PA194ModelRestoreSource.source r tail := by
    funext j; exact Fin.cases rfl (fun z => Fin.elim0 z) j
  rw [←hv,readers,getRegister,getAuxModel,fileModel]
  change getSem i.val (pi₂ (pair (modelNumeral M 31) (pack r tail))) = _
  rw [pi₂_pair]
  exact packEncodes r tail i

theorem frameSource (r : Fin 9 → M) (tail g n spare : M) :
    F (PA194ModelLoopFrameAt.frameAt 31 readers)
      (fun _ => PA194ModelLoopState.packed g n spare (PA194ModelRestoreSource.source r tail)) =
    PA194SourceSite31Physical.physicalFrame 31 g (PA194ActualLoopOrbit.frameArgs r n spare) := by
  have h := PA194ModelLoopFrameAt.modelFrameAt 31 readers g n spare (PA194ModelRestoreSource.source r tail)
  dsimp only at h
  simp only [readSource] at h
  change F (PA194ModelLoopFrameAt.frameAt 31 readers)
      (fun _ => PA194ModelLoopState.packed g n spare (PA194ModelRestoreSource.source r tail)) =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 31)
      (F zeros ![g,(1 : M)+(F sourceFileCode (PA194ActualLoopOrbit.frameArgs r n spare)+F sourceFileCode (PA194ActualLoopOrbit.frameArgs r n spare))])]]
  have hargs : PA194ActualLoopOrbit.frameArgs r n spare =
      (![r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,spare,F repeatOutput ![n,(0 : M)]] : Fin 11 → M) := by
    funext i; fin_cases i <;> simp [PA194ActualLoopOrbit.frameArgs,PA194ActualSourceLoop.args]
  rw [hargs]
  exact h
#print axioms readSource
#print axioms frameSource
end models
end PA194RestorePhysicalFrame
