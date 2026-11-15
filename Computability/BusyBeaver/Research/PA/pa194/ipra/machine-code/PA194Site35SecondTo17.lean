import PA194Site35To14
import PA194FourteenOddTo16
import PA194Site35SixteenSixRuns
import PA194HalfFileSixWithTail
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site35SecondTo17
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

noncomputable def backCost (k : M) (args : Fin 11 → M) : M :=
  let e := PA194Site35To14.vec k args
  ((((((e 5+1)+((e 4+1)+1))+((e 3+1)+1))+((e 2+1)+1))+((e 1+1)+1))+((e 0+1)+1))
noncomputable def output (k : M) (args : Fin 11 → M) : M :=
  let e := PA194Site35To14.vec k args
  let tail := F (fileCode 4) (fun i => e ⟨i.val+7,by omega⟩)
  let u := F ones ![e 6,tail]
  let r := (u+u)+(u+u)
  let w1 := F ones ![e 5,(1 : M)+r+r]
  let w2 := F ones ![e 4,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![e 3,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![e 2,(1 : M)+(w3+w3)+(w3+w3)]
  let w5 := F ones ![e 1,(1 : M)+(w4+w4)+(w4+w4)]
  F ones ![e 0,(1 : M)+(w5+w5)+(w5+w5)]

theorem to17 (k : M) (args : Fin 11 → M) :
    let out := output k args
    F PA194Stepper.stepper ![F addCode ![F addCode ![PA194Site35To14.clock k args,modelNumeral M 3],backCost k args],
      PA194SourceSite31Physical.physicalFrame 35 ((k+1)+1) args] =
      F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 201,(out+out)+(out+out)]] := by
  dsimp only
  let e := PA194Site35To14.vec k args
  let tail := F (fileCode 4) (fun i => e ⟨i.val+7,by omega⟩)
  let u := F ones ![e 6,tail]
  let r := (u+u)+(u+u)
  let l0 := modelNumeral M 804
  let x1 := F ones ![e 0+1,l0]
  let x2 := F ones ![e 1+1,x1+x1]
  let x3 := F ones ![e 2+1,x2+x2]
  let x4 := F ones ![e 3+1,x3+x3]
  let x5 := F ones ![e 4+1,x4+x4]
  let a := F ones ![e 5,x5+x5]
  have ha : F ones ![e 5+1,x5+x5] = a+a+1 := by
    dsimp only [a]
    change F ones ![F addCode ![e 5,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hq : F ones ![e 6+1,tail] = u+u+1 := by
    dsimp only [u]
    change F ones ![F addCode ![e 6,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h14 := PA194Site35To14.to14 k args
  dsimp only at h14
  change _ = F pairCode ![modelNumeral M 14,F pairCode ![
    F ones ![e 5+1,x5+x5]+F ones ![e 5+1,x5+x5],F ones ![e 6+1,tail]]] at h14
  rw [ha,hq] at h14
  have h16 := PA194FourteenOddTo16.fourteenOddTo16 a u
  dsimp only at h16
  have hs := PA194Site35SixteenSixRuns.modelSixteenSixRuns (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (modelNumeral M 402) r
  dsimp only at hs
  have h804 : modelNumeral M 402+modelNumeral M 402 = modelNumeral M 804 := by rw [←modelNumeralAdd]
  have h402 : modelNumeral M 402 = modelNumeral M 201+modelNumeral M 201 := by rw [←modelNumeralAdd]
  rw [h804,h402,(modelDouble (modelNumeral M 201)).1,(modelDouble (modelNumeral M 201)).2,zero_add] at hs
  change F PA194Stepper.stepper ![backCost k args,F pairCode ![modelNumeral M 16,F pairCode ![
    F halfCode (fun _ => a),F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]]] =
      F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 201,(output k args+output k args)+(output k args+output k args)]] at hs
  rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h14,h16,hs]
#print axioms to17
end models
end PA194Site35SecondTo17
