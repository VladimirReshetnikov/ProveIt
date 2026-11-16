import PA194Site3664To17
import PA194Site3664RootReturn
import PA194Site3664To73
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site3664FirstPass
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem firstPass (k : M) (args : Fin 11 → M) :
    let t := k
    let n := ((t+1)+1)
    let f := F sourceFileCode args
    let d := (1 : M)+(f+f)
    let v := (1 : M)+(d+d)
    let w := F ones ![t+1,v]
    let c := F addCode ![F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 1],n+1],(1 : M)]
    F PA194Stepper.stepper ![F addCode ![F addCode ![c,(t+1)+1],modelNumeral M 23],
      PA194SourceSite31Physical.physicalFrame 3664 n args] =
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 3664) w]] := by
  dsimp only
  let t := k
  let f := F sourceFileCode args
  let d := (1 : M)+(f+f)
  let v := (1 : M)+(d+d)
  let w := F ones ![t+1,v]
  have h17 := PA194Site3664To17.to17 k args
  dsimp only at h17
  have hr := PA194Site3664RootReturn.returnWord w
  rw [←PA194Site3664To73.path3664] at hr
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,modelNumeralOne] at hr
  rw [PA194StepperCompose.modelStepperCompose,h17,hr]
#print axioms firstPass
end models
end PA194Site3664FirstPass
