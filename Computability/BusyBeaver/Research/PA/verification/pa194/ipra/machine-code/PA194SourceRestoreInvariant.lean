import PA194SourceDrainInvariant
import PA194SourceFetchRestoreLoop
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194SourceRestoreInvariant
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRASubAddition
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194SourceControllerCode PA194SourceRegisterRelation PA194SchedulerFetchPositive PA194SourceFetchLoop
open PA194IteratedSimulation PA194ClockInvariantDefinable PA194ControllerRunAdd PA194SourceDrainInvariant
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def three (j : M) : M := (j+j)+j
noncomputable def argsAt (args : Fin 11 → M) (j : M) : Fin 11 → M :=
  Function.update (Function.update args 0 (args 0+j)) 6 (F subCode ![args 6,j])
noncomputable def frame (args : Fin 11 → M) (tail j : M) : M :=
  pair (modelNumeral M 31) (pair (args 0+j)
    (pair (args 1) (pair (args 2) (pair (args 3) (pair (args 4) (pair (args 5)
    (pair (F subCode ![args 6,j]) (pair (args 7) (pair (args 8) tail)))))))))

theorem frameCorrect (args : Fin 11 → M) (tail j : M) :
    frame args tail j = sourceState 31 (argsAt args j) tail := by
  simp [frame,sourceState,PA194SourceRegisterRelation.pack,regsOfArgs,argsAt]

theorem frameDef (args : Fin 11 → M) (tail : M) : 𝚺₁-Function₁ (frame args tail) := by
  let rem : M → M := fun j => F subCode ![args 6,j]
  haveI : 𝚺₁-Function₁ rem := bindLeft (fun x y : M => F subCode ![x,y]) (args 6) (binaryCodeDef (M := M) subCode)
  have hf : 𝚺₁-Function₁ (fun j : M =>
    pair (modelNumeral M 31) (pair (args 0+j)
    (pair (args 1) (pair (args 2) (pair (args 3) (pair (args 4) (pair (args 5)
    (pair (rem j) (pair (args 7) (pair (args 8) tail)))))))))) := by definability
  exact hf

theorem invariantDef (f g : M → M) (n : M) (hf : 𝚺₁-Function₁ f) (hg : 𝚺₁-Function₁ g) :
    𝚺₁-Predicate (fun j : M => n < j ∨ f (three j) = g j) := by
  haveI := hf
  haveI := hg
  dsimp only [three]
  definability
#print axioms frameCorrect
#print axioms frameDef
#print axioms invariantDef
end models
end PA194SourceRestoreInvariant
