import PA194Site32HeaderReturn
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32HeaderPass
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site32HeaderTo17 PA194Site32HeaderReturn PA194HeaderController PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194FiniteControls BinaryTapeCodes PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem firstPass (k : M) (e : Fin 11 → M) :
    let v := physicalArgs e
    let f := F sourceFileCode e
    let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let r := F zeros ![k,f+f+1]
    let a := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let w := F ones ![k+1,a]
    let c12 := F addCode ![F addCode ![modelNumeral M 8,modelNumeral M 3],(1 : M)]
    let c := (((((k+1)+1)+1)+1)+((k+1)+1))
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![F addCode ![F addCode ![F addCode ![c12,modelNumeral M 2],c],F addCode ![modelNumeral M 3,modelNumeral M 3+rc]],
      F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 32) ((r+r)+(r+r))]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),modelWord (PA194SourceProgram.path 32) w]] := by
  dsimp only
  let v := physicalArgs e
  let f := F sourceFileCode e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let r := F zeros ![k,f+f+1]
  let a := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
  let w := F ones ![k+1,a]
  have h17 := PA194Site32HeaderTo17.to17 (1 : M) k e
  dsimp only at h17
  rw [zerosTwo] at h17
  have hr := PA194Site32HeaderReturn.returnTo24 w
  dsimp only at hr
  rw [PA194StepperCompose.modelStepperCompose,h17,hr]
#print axioms firstPass
end models
end PA194Site32HeaderPass
