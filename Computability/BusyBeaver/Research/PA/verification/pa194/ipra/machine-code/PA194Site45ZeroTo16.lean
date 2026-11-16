import PA194Site45ZeroTo12
import PA194ThirteenExitComposition
import PA194ZeroReturnTo16
import PA194Site32ZeroTo14
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site45ZeroTo16
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def clock (k : M) (args : Fin 11 → M) : M :=
  let c12 := F addCode ![F addCode ![PA194Site45ZeroRollback.cost args,k+1],modelNumeral M 6]
  let c14 := ((modelNumeral M 4+1)+(k+1))+1
  let c16 := ((1 : M)+(((k+1)+1)+1))+modelNumeral M 3
  F addCode ![F addCode ![c12,c14],c16]

theorem zeroTo16 (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    let f := F sourceFileCode args
    let z := F zeros ![((k+1)+1)+1,(1 : M)+(f+f)]
    let r := (z+z)+(z+z)
    F PA194Stepper.stepper ![clock k args,PA194Site45Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 3,(1+1)+(r+r)+(r+r)]] := by
  dsimp only
  let e := physicalArgs args
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let f := F sourceFileCode args
  have hf : f=p+p := by rw [show f = F (fileCode 10) e from modelSourceFile args,modelFileSucc,modelBlock]
  have hz4 (x : M) : F zeros ![modelNumeral M 4,x] =
      (F zeros ![modelNumeral M 2,x]+F zeros ![modelNumeral M 2,x])+
      (F zeros ![modelNumeral M 2,x]+F zeros ![modelNumeral M 2,x]) := by
    change F zeros ![F Code.succ (fun _ => F Code.succ (fun _ => modelNumeral M 2)),x] = _
    rw [modelZerosSucc,modelZerosSucc]
  have hz4word (x : M) : F zeros ![modelNumeral M 4,x] =
      (((x+x)+(x+x))+((x+x)+(x+x)))+(((x+x)+(x+x))+((x+x)+(x+x))) := by
    rw [hz4,PA194HeaderController.zerosTwo]
  let l := modelNumeral M 13
  let z2 := F zeros ![modelNumeral M 2,l]
  have hleft : F zeros ![k+1,F zeros ![modelNumeral M 4,l]+F zeros ![modelNumeral M 4,l]] =
      F zeros ![((k+1)+1)+1,z2+z2] := by
    rw [hz4]
    rw [show ((k+1)+1)+1 = F Code.succ (fun _ => (k+1)+1) from modelAddOne _,modelZerosSucc]
    rw [show (k+1)+1 = F Code.succ (fun _ => k+1) from modelAddOne _,modelZerosSucc]
    simp only [PA194ZerosDouble.modelZerosDouble]
    dsimp only [z2]
  have h12 := PA194Site45ZeroTo12.zeroTo12 k args hz
  dsimp only at h12
  have hs := PA194ThirteenExitComposition.modelTwoScansExit (modelNumeral M 4) (k+1) l p
  rw [←hf] at hs
  simp only [hz4word] at hs
  have h14' : F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![PA194Site45ZeroRollback.cost args,k+1],modelNumeral M 6],
      ((modelNumeral M 4+1)+(k+1))+1],PA194Site45Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 14,F pairCode ![
        F halfCode (fun _ => F zeros ![k+1,F zeros ![modelNumeral M 4,l]+F zeros ![modelNumeral M 4,l]]),
        F parityCode (fun _ => F zeros ![k+1,F zeros ![modelNumeral M 4,l]+F zeros ![modelNumeral M 4,l]])+f+f]] := by
    simp only [hz4word]
    rw [PA194StepperCompose.modelStepperCompose,h12,hs]
  have h16 := PA194ZeroReturnTo16.from14To16 ((k+1)+1) (modelNumeral M 6) p
  dsimp only at h16
  have h13 : modelNumeral M 6+modelNumeral M 6+1 = modelNumeral M 13 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have h6 : modelNumeral M 6 = modelNumeral M 3+modelNumeral M 3 := by rw [←modelNumeralAdd]
  rw [h13,←hf,h6,(modelDouble (modelNumeral M 3)).1,(modelDouble (modelNumeral M 3)).2,zero_add] at h16
  have hsum : (1 : M)+f+f = (1 : M)+(f+f) := by simp only [add_assoc]
  rw [hsum] at h16
  rw [hleft] at h14'
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h14',h16]
#print axioms zeroTo16
end models
end PA194Site45ZeroTo16
