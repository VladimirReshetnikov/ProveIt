import PA194SeedHeaderDispatch
import PA194EightyFourTo17
import PA194RegisterPermutation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SeedHeaderTo17
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194RegisterPermutation PA194RegisterFile PA194UnaryRuns PA194ZeroRuns
open PA194SeedHeaderDispatch PA194EightyFourTo17 PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- The seeded source-header route through state 17 for arbitrary source-file
values, header length and left tape, including nonstandard model elements. -/
theorem sourceHeaderTo17 (l k : M) (e : Fin 11 → M) :
    let v := physicalArgs e
    let f := F sourceFileCode e
    let r := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
    let s := F zeros ![k,f+f+1]
    let y0 := s+s
    let y1 := y0+y0
    let y2 := y1+y1
    let y3 := y2+y2
    let y4 := y3+y3
    let y5 := y4+y4
    let y6 := y5+y5
    let a0 := l+l+1
    let a1 := a0+a0
    let a2 := a1+a1
    let a3 := a2+a2
    let a4 := a3+a3
    let t := (1 : M)+(1+1)+((r+r)+(r+r))+((r+r)+(r+r))
    let w := F ones ![k+1,t]
    let clock := modelNumeral M 12 + (((((k+1)+1)+1)+1)+((k+1)+1))
    F PA194Stepper.stepper ![clock,F pairCode ![modelNumeral M 24,F pairCode ![l,y6+y6+1]]] =
      F pairCode ![modelNumeral M 17,F pairCode ![F BinaryTapeCodes.halfCode (fun _ => a4),
        F BinaryTapeCodes.parityCode (fun _ => a4)+(w+w)+(w+w)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let v := physicalArgs e
  let f := F sourceFileCode e
  let r := F ones ![v 0+1,F (fileCode 9) (fun i => v i.succ)]
  let s := F zeros ![k,f+f+1]
  let a0 := l+l+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3
  let c := (((((k+1)+1)+1)+1)+((k+1)+1))
  have hf : f=r+r := by
    rw [show f = F (fileCode 10) v from modelSourceFile e,modelFileSucc,modelBlock]
  have ht : f+f+1 = (1 : M)+(r+r)+(r+r) := by
    rw [hf]
    simp only [add_comm,add_left_comm]
  have h84 := twelveSteps l s
  dsimp only at h84
  have h17 := returnedFileTo17 k a4 r
  dsimp only at h17
  rw [←ht,PA194HeaderController.zerosTwo] at h17
  change F PA194Stepper.stepper ![c,
    F pairCode ![modelNumeral M 84,F pairCode ![a4+a4,(s+s)+(s+s)]]] = _ at h17
  change F PA194Stepper.stepper ![F addCode ![modelNumeral M 12,c],_] = _
  rw [PA194StepperCompose.modelStepperCompose,h84,h17]
#print axioms sourceHeaderTo17
end models
end PA194SeedHeaderTo17
