import PA194SourceSite38DrainStep
import PA194Site38PositiveClockExists
import PA194Site39ClockExists
import PA194SourceSite40Physical
import PA194Site38PositivePath
import PA194SourceSite38Controller
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace PA194SourceSite38DrainSingle
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

theorem drainSingle (k count tail m : M) (args : Fin 11 → M)
    (hm : args 7 = m+1)
    (he : PA194RegisterPermutation.physicalArgs args 10 = F PA194OneSpareReturn.repeatOutput ![count,(0 : M)]) :
    let out := PA194Site39OutputFile.updated (Function.update args 7 m) count
    ∃ c : M,
      F step ![F step ![F step ![sourceState 38 args tail]]] = sourceState 38 out tail ∧
      F PA194Stepper.stepper ![c,physicalFrame 38 ((k+1)+1) args] =
        physicalFrame 38 (((k+1)+1)+1) out := by
  obtain ⟨c38,c39,hcontroller,hphysical⟩ := PA194SourceSite38DrainStep.drainStep k count tail m args hm he
  refine ⟨F addCode ![F addCode ![c38,c39],modelNumeral M 40],hcontroller,?_⟩
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hphysical]
#print axioms drainSingle
end models
end PA194SourceSite38DrainSingle
