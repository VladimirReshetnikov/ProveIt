import PA194Site34To14Exact
import PA194FourteenOddTo16
import PA194SixteenTwoRuns
set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
namespace PA194Site34SecondTo17
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194RightRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def to14Clock (k : M) (args : Fin 11 → M) : M :=
  let n := (k+1)+1
  let e := physicalArgs args
  let c := F addCode ![F addCode ![modelNumeral M 13,n+1],(1 : M)]
  let first := F addCode ![F addCode ![c,(k+1)+1],modelNumeral M 23]
  let second := F addCode ![first,modelNumeral M 8]
  let third := F addCode ![F addCode ![second,k],modelNumeral M 3]
  F addCode ![third,(e 0+1)+1]

theorem to17 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let tail := F (fileCode 8) (fun i => e i.succ.succ)
    let u := F ones ![e 1,tail]
    let c := (u+u)+(u+u)
    let w := F ones ![e 0,(1 : M)+c+c]
    let out := F ones ![k+1,(1 : M)+(w+w)+(w+w)]
    let back := (e 0+1)+(((k+1)+1)+1)
    F PA194Stepper.stepper ![F addCode ![F addCode ![to14Clock k args,modelNumeral M 3],back],
      PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 100,(out+out)+(out+out)]] := by
  dsimp only
  let e := physicalArgs args
  let tail := F (fileCode 8) (fun i => e i.succ.succ)
  let u := F ones ![e 1,tail]
  let c := (u+u)+(u+u)
  let b := F ones ![k,modelNumeral M 400]
  let a1 := b+b+1
  let a2 := a1+a1+1
  let a3 := a2+a2
  let left := F ones ![e 0,a3]
  let q := F ones ![e 1+1,tail]
  let w := F ones ![e 0,(1 : M)+c+c]
  let out := F ones ![k+1,(1 : M)+(w+w)+(w+w)]
  let back := (e 0+1)+(((k+1)+1)+1)
  have hl : F ones ![e 0+1,a3] = left+left+1 := by
    dsimp only [left]
    change F ones ![F addCode ![e 0,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hq : q = u+u+1 := by
    dsimp only [q,u]
    change F ones ![F addCode ![e 1,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h14 := PA194Site34To14Exact.to14 k args
  dsimp only at h14
  change F PA194Stepper.stepper ![to14Clock k args,PA194SourceSite31Physical.physicalFrame 34 ((k+1)+1) args] =
    F pairCode ![modelNumeral M 14,F pairCode ![(F ones ![e 0+1,a3])+(F ones ![e 0+1,a3]),q]] at h14
  rw [hl,hq] at h14
  have h16 := PA194FourteenOddTo16.fourteenOddTo16 left u
  dsimp only at h16
  have h400 : modelNumeral M 200+modelNumeral M 200 = modelNumeral M 400 := by rw [←modelNumeralAdd]
  have ha2 : F ones ![(k+1)+1,modelNumeral M 400] = a2 := by
    rw [show (k+1)+1 = F Code.succ (fun _ => k+1) from modelAddOne _,modelOnesSucc,
      show k+1 = F Code.succ (fun _ => k) from modelAddOne _,modelOnesSucc]
  have hback := PA194SixteenTwoRuns.modelSixteenTwoRuns (e 0) (k+1) (modelNumeral M 200) c
  dsimp only at hback
  rw [h400,ha2] at hback
  have h200 : modelNumeral M 200 = modelNumeral M 100+modelNumeral M 100 := by rw [←modelNumeralAdd]
  rw [h200,(modelDouble (modelNumeral M 100)).1,(modelDouble (modelNumeral M 100)).2,zero_add] at hback
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h14,h16,hback]
#print axioms to17
end models
end PA194Site34SecondTo17
