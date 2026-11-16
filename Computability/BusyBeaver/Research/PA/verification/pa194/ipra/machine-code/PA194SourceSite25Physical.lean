import PA194SourceControllerStep
import PA194SourceRegisterRelation
import PA194SourcePCBound
import PA194Path25To27
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceSite25Physical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceControllerStep PA194SourceRegisters
open PA194SourceRegisterRelation PA194SourcePCBound PA194RegisterPermutation PA194ZeroRuns PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

def regsOfArgs (args : Fin 11 → M) (i : Fin 9) : M := args ⟨i.val,by have h := i.isLt; omega⟩
noncomputable def sourceState (q : Nat) (args : Fin 11 → M) (tail : M) : M :=
  pair (modelNumeral M q) (pack (regsOfArgs args) tail)
noncomputable def physicalFrame (q : Nat) (gap : M) (args : Fin 11 → M) : M :=
  let f := F sourceFileCode args
  F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
    modelWord (PA194SourceProgram.path q) (F zeros ![gap,(1 : M)+(f+f)])]]

/-- A matched site-25 source/physical frame follows its zero branch to the
    matched site-27 frames, for arbitrary model register values and tails. -/
theorem zeroBranch (k tail : M) (args : Fin 11 → M) (hz : args 8 = (0 : M)) :
    F step ![sourceState 25 args tail] = sourceState 27 args tail ∧
      ∃ clock : M, F PA194Stepper.stepper ![clock,physicalFrame 25 ((k+1)+1) args] =
        physicalFrame 27 (k+1) args := by
  have hpc : F pc ![sourceState 25 args tail] = modelNumeral M 25 := by
    rw [pcModel]
    exact pi₁_pair _ _
  have hreg : getSem 8 (pi₂ (sourceState 25 args tail)) = (0 : M) := by
    change getSem 8 (pi₂ (pair (modelNumeral M 25) (pack (regsOfArgs args) tail))) = 0
    rw [pi₂_pair]
    have h := packEncodes (regsOfArgs args) tail (8 : Fin 9)
    change getSem 8 (pack (regsOfArgs args) tail) = args 8 at h
    exact h.trans hz
  constructor
  · rw [site25Zero _ hpc hreg]
    change pair (modelNumeral M 27) (pi₂ (pair (modelNumeral M 25) (pack (regsOfArgs args) tail))) = _
    rw [pi₂_pair]
    rfl
  · exact ⟨_, PA194Path25To27.zeroBranchPath25To27 k args hz⟩
#print axioms zeroBranch
end models
end PA194SourceSite25Physical
