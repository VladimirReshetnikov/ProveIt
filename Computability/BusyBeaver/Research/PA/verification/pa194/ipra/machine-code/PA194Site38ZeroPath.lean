import PA194Site38ZeroTo16New
import PA194Site38ZeroReturn
import PA194Site32ZeroPath
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site38ZeroPath
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing

theorem path41 : PA194SourceProgram.path 41 = [true,false,false,true,false,false,true,true,true] := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem zeroPath (k : M) (args : Fin 11 → M) (hz : args 7 = (0 : M)) :
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![F addCode ![F addCode ![PA194Site38ZeroRollback.cost args,k+1],modelNumeral M 5],((modelNumeral M 3+1)+(k+1))+1],((1 : M)+((k+1)+1))+modelNumeral M 3],modelNumeral M 25],
      PA194Site38Branch.runTo4 k args] =
      PA194SourceSite31Physical.physicalFrame 41 ((((k+1)+1)+1)+1) args := by
  let f := F sourceFileCode args
  let z := F zeros ![(k+1)+1,(1 : M)+(f+f)]
  let r := (z+z)+(z+z)
  have h16 := PA194Site38ZeroTo16New.zeroTo16 k args hz
  dsimp only at h16
  change F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![F addCode ![PA194Site38ZeroRollback.cost args,k+1],modelNumeral M 5],((modelNumeral M 3+1)+(k+1))+1],((1 : M)+((k+1)+1))+modelNumeral M 3],
      PA194Site38Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 201,(1+1+1)+(r+r)+(r+r)]] at h16
  have hr := PA194Site38ZeroReturn.returnWord z
  have hinput : modelWord [true,true,false,false] z = (1+1+1)+(r+r)+(r+r) := by
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
    dsimp only [r]
    ac_rfl
  rw [hinput] at hr
  simp only [modelNumeralOne] at hr
  have hzrun : F zeros ![(((k+1)+1)+1)+1,(1 : M)+(f+f)] = r := by
    dsimp only [z,r]
    rw [PA194Site32ZeroPath.zerosSucc,PA194Site32ZeroPath.zerosSucc]
  have hword : modelWord [true,false,false,true,false,false,true,true,true,false,false] z =
      modelWord (PA194SourceProgram.path 41) (F zeros ![(((k+1)+1)+1)+1,(1 : M)+(f+f)]) := by
    rw [path41,hzrun]
    dsimp only [r]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  rw [hword] at hr
  rw [PA194StepperCompose.modelStepperCompose,h16,hr]
  rfl
#print axioms path41
#print axioms zeroPath
end models
end PA194Site38ZeroPath
