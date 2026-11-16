import PA194Site3668ZeroTo12
import PA194ThirteenExitComposition
import PA194FirstThreeBlankTailTo16
import PA194ZerosDouble
import PA194Site32ZeroTo14
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3668ZeroTo16
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
  let m := (((((k+1)+1)+1)+1)+1)
  let c12 := F addCode ![F addCode ![PA194Site3668ZeroRollback.cost args,k+1],modelNumeral M 8]
  let c14 := ((modelNumeral M 6+1)+(k+1))+1
  let c16 := ((1 : M)+m)+modelNumeral M 3
  F addCode ![F addCode ![c12,c14],c16]

theorem zeroTo16 (k : M) (args : Fin 11 → M) (hz : args 6 = (0 : M)) :
    let f := F sourceFileCode args
    let m := (((((k+1)+1)+1)+1)+1)
    let z := F zeros ![m,(1 : M)+(f+f)]
    let r := (z+z)+(z+z)
    F PA194Stepper.stepper ![clock k args,PA194Site3668Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 1,(1+1+1)+(r+r)+(r+r)]] := by
  dsimp only
  let s := k+1
  let m := ((((s+1)+1)+1)+1)
  let e := physicalArgs args
  let p := F ones ![e 0+1,F (fileCode 9) (fun i => e i.succ)]
  let f := F sourceFileCode args
  have hf : f=p+p := by rw [show f = F (fileCode 10) e from modelSourceFile args,modelFileSucc,modelBlock]
  have h12 := PA194Site3668ZeroTo12.zeroTo12 k args hz
  dsimp only at h12
  have hs := PA194ThirteenExitComposition.modelTwoScansExit (modelNumeral M 6) s (modelNumeral M 7) p
  rw [←hf] at hs
  have h14 : F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![PA194Site3668ZeroRollback.cost args,s],modelNumeral M 8],
      ((modelNumeral M 6+1)+s)+1],PA194Site3668Branch.runTo4 k args] =
      F pairCode ![modelNumeral M 14,F pairCode ![
        F halfCode (fun _ => F zeros ![s,F zeros ![modelNumeral M 6,modelNumeral M 7]+F zeros ![modelNumeral M 6,modelNumeral M 7]]),
        F parityCode (fun _ => F zeros ![s,F zeros ![modelNumeral M 6,modelNumeral M 7]+F zeros ![modelNumeral M 6,modelNumeral M 7]])+f+f]] := by
    rw [PA194StepperCompose.modelStepperCompose,h12,hs]
  have hn : F zeros ![modelNumeral M 6,modelNumeral M 7] = modelNumeral M 448 := by
    rw [←PA194HeaderController.zerosSix]
    simp only [←modelNumeralAdd]
  have zs (n x : M) : F zeros ![n+1,x] = F zeros ![n,x]+F zeros ![n,x] := by
    rw [show n+1 = F Code.succ (fun _ => n) from modelAddOne n,modelZerosSucc]
  have hy : F zeros ![m,modelNumeral M 14] = F zeros ![s,modelNumeral M 224] := by
    dsimp only [m]
    rw [zs,zs,zs,zs,←PA194ZerosDouble.modelZerosDouble,←PA194ZerosDouble.modelZerosDouble,
      ←PA194ZerosDouble.modelZerosDouble,←PA194ZerosDouble.modelZerosDouble]
    simp only [←modelNumeralAdd]
  let v := F zeros ![s,modelNumeral M 448]
  have hleft : F zeros ![s,F zeros ![modelNumeral M 6,modelNumeral M 7]+F zeros ![modelNumeral M 6,modelNumeral M 7]] = v+v := by
    rw [hn,PA194ZerosDouble.modelZerosDouble]
  rw [hleft,(modelDouble v).1,(modelDouble v).2,zero_add] at h14
  have hmy : F zeros ![m,modelNumeral M 14]+F zeros ![m,modelNumeral M 14] = v := by
    rw [hy,←PA194ZerosDouble.modelZerosDouble]
    dsimp only [v]
    simp only [←modelNumeralAdd]
  have h16 := PA194FirstThreeBlankTailTo16.header14To16 m (modelNumeral M 3) p
  dsimp only at h16
  have h3 : modelNumeral M 3+modelNumeral M 3+1 = modelNumeral M 7 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [h3,←modelNumeralAdd,hmy] at h16
  have hn3 : modelNumeral M 3 = modelNumeral M 1+modelNumeral M 1+1 := by rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  rw [hn3,(modelOdd (modelNumeral M 1)).1,(modelOdd (modelNumeral M 1)).2,←hf] at h16
  have hsum : (1 : M)+f+f = (1 : M)+(f+f) := by simp only [add_assoc]
  rw [hsum,←hn3] at h16
  dsimp only [clock]
  rw [PA194StepperCompose.modelStepperCompose,h14,h16]
  dsimp only [m,s,f]
  simp only [add_assoc]
#print axioms zeroTo16
end models
end PA194Site3668ZeroTo16
