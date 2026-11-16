import PA194Site39OutputFile
import PA194ActualLoopOrbit
import Mathlib.Tactic.FinCases
import PA194Transfer42PhysicalExit
import PA194Transfer45PhysicalExit
import PA194SeedFirstSite3661
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace PA194IncrementFrameInvariant
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194OneSpareReturn PRASubAddition PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194StateOne PA194FiniteControls PA194ModelLoopIteration PA194RegisterPermutation PA194SourceSite31Physical PA194ModelTransferState TableDispatch PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem incrementPreservesFrame (r : Fin 9 → M) (count spare : M) :
    PA194Site39OutputFile.updated (PA194ActualLoopOrbit.frameArgs r count spare) count =
      PA194ActualLoopOrbit.frameArgs (Function.update r 6 (r 6+1)) (count+1) spare := by
  funext i
  fin_cases i <;> simp [PA194Site39OutputFile.updated,PA194ActualLoopOrbit.frameArgs,
    PA194ActualSourceLoop.args,Function.update]
  rw [←modelAddOne]
  rfl
#print axioms incrementPreservesFrame
end models
end PA194IncrementFrameInvariant
