import PA194ActualSourceRun
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194ActualSourceExit
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194ModelLoopIteration PA194ModelSourceLoop PA194ActualSourceLoop PA194ActualSourceRun PA194StateOne BinaryTapeCodes TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters PA194SourceRegisterRelation PA194SourcePCBound PA194SourceSite25Physical
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem zeroStep (r : Fin 9 → M) (tail : M) (hzero : r 0 = (0 : M)) :
    F step ![PA194ModelSourceLoop.source r tail] = sourceState 31 (PA194ActualSourceLoop.args r) tail := by
  rw [←PA194ActualSourceLoop.sourceEq]
  have hpc : F pc ![sourceState 27 (PA194ActualSourceLoop.args r) tail] = modelNumeral M 27 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 0 (pi₂ (sourceState 27 (PA194ActualSourceLoop.args r) tail)) = (0 : M) := by
    change getSem 0 (pi₂ (pair (modelNumeral M 27) (pack (regsOfArgs (PA194ActualSourceLoop.args r)) tail))) = 0
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs (PA194ActualSourceLoop.args r)) tail (0 : Fin 9)
    change getSem 0 (pack (regsOfArgs (PA194ActualSourceLoop.args r)) tail) = r 0 at h
    exact h.trans hzero
  rw [actualInstructionStep 27 (by decide) _ hpc,PA194SourceSite27Physical.site27Instruction]
  simp only [PA194SourceInstructionModel.instructionSem,PA194SourceControllerCode.destination]
  change (if getSem 0 (pi₂ (sourceState 27 (PA194ActualSourceLoop.args r) tail)) = (0 : M) then _ else _) = _
  rw [if_pos hreg]
  change pair (modelNumeral M 31) (pi₂ (pair (modelNumeral M 27) (pack (regsOfArgs (PA194ActualSourceLoop.args r)) tail))) = _
  rw [pi₂_pair]
  rfl
theorem exitsAt31 (r : Fin 9 → M) (tail : M) :
    let n := r 0
    let t := (n+n)+(n+n)
    let out := PA194ModelSourceLoop.running r n
    F PA194SourceControllerCode.run ![F Code.succ (fun _ => t),PA194ModelSourceLoop.source r tail] =
      sourceState 31 (PA194ActualSourceLoop.args out) tail := by
  dsimp only
  have h := PA194ActualSourceRun.reachesZero r tail
  dsimp only at h
  have hs := zeroStep (PA194ModelSourceLoop.running r (r 0)) tail h.2.1
  change F (iterCode step) ![F Code.succ (fun _ => (r 0+r 0)+(r 0+r 0)),PA194ModelSourceLoop.source r tail] = _
  rw [modelIterSucc]
  have hv (x : M) : (![x] : Fin 1 → M) = fun _ => x := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [←hv]
  change F step ![F PA194SourceControllerCode.run ![(r 0+r 0)+(r 0+r 0),PA194ModelSourceLoop.source r tail]] = _
  rw [h.1,hs]
#print axioms zeroStep
#print axioms exitsAt31
end models
end PA194ActualSourceExit
