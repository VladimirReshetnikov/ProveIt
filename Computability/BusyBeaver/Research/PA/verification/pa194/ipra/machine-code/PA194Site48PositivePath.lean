import PA194Site48PositiveTo16
import PA194Site48PositiveFinish
import PA194Site32ZeroPath
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site48PositivePath
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing

theorem path49 : PA194SourceProgram.path 49 = [true,false,true,false,true,false,false,false] := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem positivePath (k m : M) (args : Fin 11 → M) (hm : args 3 = m+1) :
    F PA194Stepper.stepper ![F addCode ![PA194Site48PositiveTo16.clock k args,modelNumeral M 21],
      PA194Site48Branch.runTo4 k args] =
      PA194SourceSite31Physical.physicalFrame 49 k (Function.update args 3 m) := by
  let f := F sourceFileCode (Function.update args 3 m)
  let z := F zeros ![k+1,(1 : M)+(f+f)]
  let r := (z+z)+(z+z)
  have h16 := PA194Site48PositiveTo16.positiveTo16 k m args hm
  dsimp only at h16
  change F PA194Stepper.stepper ![PA194Site48PositiveTo16.clock k args,
      PA194Site48Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 13,(1+1)+(r+r)+(r+r)]] at h16
  have hr := PA194Site48PositiveFinish.returnWord z
  have hinput : modelWord [false,true,false,false] z = (1+1)+(r+r)+(r+r) := by
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
    dsimp only [r]
    ac_rfl
  rw [hinput] at hr
  simp only [modelNumeralOne] at hr
  have hzrun : z = F zeros ![k,(1 : M)+(f+f)]+F zeros ![k,(1 : M)+(f+f)] := by
    dsimp only [z]
    rw [PA194Site32ZeroPath.zerosSucc]
  have hword : modelWord [true,false,true,false,true,false,false] z =
      modelWord (PA194SourceProgram.path 49) (F zeros ![k,(1 : M)+(f+f)]) := by
    rw [path49,hzrun]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  rw [hword] at hr
  rw [PA194StepperCompose.modelStepperCompose,h16,hr]
  rfl
#print axioms path49
#print axioms positivePath
end models
end PA194Site48PositivePath
