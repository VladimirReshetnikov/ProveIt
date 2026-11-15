import PA194Site42GapPrefix
import PA194Site42To30
import PA194EightyFourScan
import PA194LeftRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site42To15
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194LeftRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem row59zero (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 1,F pairCode ![modelNumeral M 59,F pairCode ![modelNumeral M 404,x+x]]] =
      F pairCode ![modelNumeral M 84,F pairCode ![modelNumeral M 202,(x+x)+(x+x)]] := by
  have h := leftZero 59 84 (by decide) (by decide +kernel) (modelNumeral M 404) x
  have hn : modelNumeral M 404 = modelNumeral M 202+modelNumeral M 202 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 404) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 202)).1]
  have hh : F halfCode (fun _ => modelNumeral M 404) = modelNumeral M 202 := by rw [hn,(modelDouble (modelNumeral M 202)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
  rw [PA194Stepper.modelStepperSucc,show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero,h]
  simp only [zero_add]

theorem to15 (gap : M) (args : Fin 11 → M) :
    let n := (gap+1)+1
    let a := F ones ![n,modelNumeral M 202]
    let f := F sourceFileCode args
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![modelNumeral M 7,modelNumeral M 3],modelNumeral M 1],n+1],
      PA194SourceSite31Physical.physicalFrame 42 n args] =
      F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => a),
        F parityCode (fun _ => a)+(1+1)+(f+f)+(f+f)]] := by
  dsimp only
  let n := (gap+1)+1
  let f := F sourceFileCode args
  let x := F zeros ![gap,(1 : M)+(f+f)]
  have hz1 : F zeros ![gap+1,(1 : M)+(f+f)] = x+x := by dsimp only [x]; rw [PA194Site32ZeroPath.zerosSucc]
  have hz2 : F zeros ![n,(1 : M)+(f+f)] = (x+x)+(x+x) := by dsimp only [n]; rw [PA194Site32ZeroPath.zerosSucc,hz1]
  have hd := PA194Site42To30.to30 n args
  dsimp only at hd
  have hgap := PA194Site42GapPrefix.prefixWord (F zeros ![gap+1,(1 : M)+(f+f)])
  simp only [modelWord,Bool.false_eq_true,↓reduceIte] at hgap
  rw [hz2] at hd
  rw [←hz1] at hd
  have hscan := PA194EightyFourScan.scanExit n (modelNumeral M 202) f
  dsimp only at hscan
  have hr : (1 : M)+(f+f) = f+f+1 := by ac_rfl
  rw [←hr,hz2] at hscan
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,hd,hgap,hz1,row59zero,hscan]
#print axioms row59zero
#print axioms to15
end models
end PA194Site42To15
