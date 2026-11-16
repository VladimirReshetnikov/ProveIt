import PA194Site34PositiveTo16
import PA194Site34PositiveFinish
import PA194Site32ZeroPath
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site34PositivePath
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing

theorem path35 : PA194SourceProgram.path 35 = [true,false,false,true,false,false,true,false] := by decide +kernel
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem positivePath (k m : M) (args : Fin 11 → M) (hm : args 8 = m+1) :
    F PA194Stepper.stepper ![F addCode ![PA194Site34PositiveTo16.clock k args,modelNumeral M 23],
      PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      PA194SourceSite31Physical.physicalFrame 35 ((k+1)+1) (Function.update args 8 m) := by
  let f := F sourceFileCode (Function.update args 8 m)
  let z := F zeros ![k+1,(1 : M)+(f+f)]
  let r := (z+z)+(z+z)
  have h16 := PA194Site34PositiveTo16.positiveTo16 k m args hm
  dsimp only at h16
  change F PA194Stepper.stepper ![PA194Site34PositiveTo16.clock k args,
      PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 50,(1+1)+(r+r)+(r+r)]] at h16
  have hr := PA194Site34PositiveFinish.returnWord r
  have hinput : modelWord [false,true] r = (1+1)+(r+r)+(r+r) := by
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
    ac_rfl
  rw [hinput] at hr
  simp only [modelNumeralOne] at hr
  have hzrun : F zeros ![(k+1)+1,(1 : M)+(f+f)] = z+z := by
    dsimp only [z]
    rw [PA194Site32ZeroPath.zerosSucc]
  have hword : modelWord [true,false,false,true,false,false,true] r =
      modelWord (PA194SourceProgram.path 35) (F zeros ![(k+1)+1,(1 : M)+(f+f)]) := by
    rw [path35,hzrun]
    dsimp only [r]
    simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false]
  rw [hword] at hr
  rw [PA194StepperCompose.modelStepperCompose,h16,hr]
  rfl
#print axioms path35
#print axioms positivePath
end models
end PA194Site34PositivePath
