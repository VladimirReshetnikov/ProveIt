import PA194ModelLoopFrame
import PA194SourceRegisterRelation
import PA194SourceInstructionModel
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ControllerLoopFrame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopState PA194ModelLoopFrame PA194OneSpareReturn PA194StateOne PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194FiniteControls PA194RegisterFile PA194RegisterPermutation PA194Path27Header BinaryTapeCodes PackedDecoderModel TableDispatch
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
def regsOfArgs (args : Fin 11 → M) (i : Fin 9) : M := args ⟨i.val,by have h := i.isLt; omega⟩
noncomputable def source (args : Fin 11 → M) (tail : M) : M := pair (modelNumeral M 27) (pack (regsOfArgs args) tail)
def readers : Fin 9 → Code 1 := fun i => getRegister i.val
theorem readSource (args : Fin 11 → M) (tail : M) (i : Fin 9) :
    F (readers i) (fun _ => source args tail) = regsOfArgs args i := by
  have hv : (![source args tail] : Fin 1 → M) = fun _ => source args tail := by
    funext j; exact Fin.cases rfl (fun z => Fin.elim0 z) j
  rw [←hv,readers,getRegister,getAuxModel,fileModel]
  change getSem i.val (pi₂ (pair (modelNumeral M 27) (pack (regsOfArgs args) tail))) = _
  rw [pi₂_pair]
  exact packEncodes (regsOfArgs args) tail i
theorem frameSource (args : Fin 11 → M) (g n tail : M)
    (htail : args 10 = F repeatOutput ![n,(0 : M)]) :
    F (PA194ModelLoopFrame.frame readers) (fun _ => packed g n (args 9) (source args tail)) =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 27)
        (F zeros ![g,(1 : M)+(F sourceFileCode args+F sourceFileCode args)])]] := by
  have h := modelFrame readers g n (args 9) (source args tail)
  dsimp only at h
  have hv : (![F (readers 0) (fun _ => source args tail),F (readers 1) (fun _ => source args tail),F (readers 2) (fun _ => source args tail),F (readers 3) (fun _ => source args tail),F (readers 4) (fun _ => source args tail),F (readers 5) (fun _ => source args tail),F (readers 6) (fun _ => source args tail),F (readers 7) (fun _ => source args tail),F (readers 8) (fun _ => source args tail),args 9,F repeatOutput ![n,(0 : M)]] : Fin 11 → M) = args := by
    funext i
    fin_cases i <;> simp [readSource,regsOfArgs,←htail]
  rw [hv] at h
  exact h
#print axioms readSource
#print axioms frameSource
end models
end PA194ControllerLoopFrame
