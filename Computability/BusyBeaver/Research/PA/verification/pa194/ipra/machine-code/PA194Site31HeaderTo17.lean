import PA194Site31HeaderTo84
import PA194EightyFourTo17
import PA194RegisterPermutation
import PA194HeaderController
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31HeaderTo17
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site31HeaderTo84 PA194EightyFourTo17 PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194HeaderController BinaryTapeCodes PRAModelIOpenPairing PA194Path27Header
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem site31HeaderTo17 (l k : M) (e : Fin 11 → M) :
    let v := physicalArgs e
    let f := F sourceFileCode e
    let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let r := F zeros ![k,f+f+1]
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3+1
    let t := (1 : M)+(1+1)+((p+p)+(p+p))+((p+p)+(p+p))
    let w := F ones ![k+1,t]
    let clock15 := F addCode ![F addCode ![modelNumeral M 7,modelNumeral M 3],modelNumeral M 5]
    let c := (((((k+1)+1)+1)+1)+((k+1)+1))
    F PA194Stepper.stepper ![F addCode ![clock15,c],F pairCode ![modelNumeral M 24,
      F pairCode ![l,modelWord (PA194SourceProgram.path 31) ((r+r)+(r+r))]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![a4,(1 : M)+(w+w)+(w+w)]] := by
  dsimp only
  let v := physicalArgs e
  let f := F sourceFileCode e
  let p := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let r := F zeros ![k,f+f+1]
  let a0 := l+l+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4+1
  let c := (((((k+1)+1)+1)+1)+((k+1)+1))
  have hf : f=p+p := by rw [show f = F (fileCode 10) v from modelSourceFile e,modelFileSucc,modelBlock]
  have ht : f+f+1 = (1 : M)+(p+p)+(p+p) := by rw [hf]; simp only [add_comm,add_left_comm]
  have h84 := PA194Site31HeaderTo84.to84 l r
  dsimp only at h84
  have h17 := returnedFileTo17 k a5 p
  dsimp only at h17
  rw [←ht,zerosTwo,(modelOdd a4).1,(modelOdd a4).2] at h17
  rw [PA194StepperCompose.modelStepperCompose,h84,h17]
#print axioms site31HeaderTo17
end models
end PA194Site31HeaderTo17
