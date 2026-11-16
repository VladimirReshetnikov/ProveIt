import PA194Site42SecondTo14
import PA194FourteenOddTo16
import PA194Site35SixteenSixRuns
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site42SecondTo17
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterPermutation PA194RegisterFile BinaryTapeCodes TableDispatch PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def output (k : M) (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  let tail := F (fileCode 4) (fun i => e ⟨i.val+6,by omega⟩)
  let u := F ones ![e 5,tail]
  let r := (u+u)+(u+u)
  let w1 := F ones ![e 4,(1 : M)+r+r]
  let w2 := F ones ![e 3,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![e 2,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![e 1,(1 : M)+(w3+w3)+(w3+w3)]
  let w5 := F ones ![e 0,(1 : M)+(w4+w4)+(w4+w4)]
  F ones ![k+1,(1 : M)+(w5+w5)+(w5+w5)]
theorem to17 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let out := output k args
    F PA194Stepper.stepper ![((k+1)+1)+1,
      F PA194Stepper.stepper ![(e 0+1)+1,
        F PA194Stepper.stepper ![(e 1+1)+1,
          F PA194Stepper.stepper ![(e 2+1)+1,
            F PA194Stepper.stepper ![(e 4+1)+((e 3+1)+1),
              F PA194Stepper.stepper ![modelNumeral M 3,
                F PA194Stepper.stepper ![PA194Site42SecondTo14.clock k args,
                  PA194SourceSite31Physical.physicalFrame 42 ((k+1)+1) args]]]]]]] =
      F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 101,(out+out)+(out+out)]] := by
  dsimp only
  let e := physicalArgs args
  let tail := F (fileCode 4) (fun i => e ⟨i.val+6,by omega⟩)
  let u := F ones ![e 5,tail]
  let r := (u+u)+(u+u)
  let b := PA194Site42SecondTo14.lefts k args 0
  let x1 := PA194Site42SecondTo14.lefts k args 1
  let x2 := PA194Site42SecondTo14.lefts k args 2
  let x3 := PA194Site42SecondTo14.lefts k args 3
  let x4 := PA194Site42SecondTo14.lefts k args 4
  let a := F ones ![e 4,x4+x4]
  let w1 := F ones ![e 4,(1 : M)+r+r]
  let w2 := F ones ![e 3,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![e 2,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![e 1,(1 : M)+(w3+w3)+(w3+w3)]
  let w5 := F ones ![e 0,(1 : M)+(w4+w4)+(w4+w4)]
  have ha : PA194Site42SecondTo14.lefts k args 5 = a+a+1 := by
    dsimp only [PA194Site42SecondTo14.lefts,a,x4]
    change F ones ![F addCode ![e 4,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
    rfl
  have hq : F ones ![e 5+1,tail] = u+u+1 := by
    dsimp only [u]
    change F ones ![F addCode ![e 5,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h14 := PA194Site42SecondTo14.to14 k args
  dsimp only at h14
  change _ = F pairCode ![modelNumeral M 14,F pairCode ![PA194Site42SecondTo14.lefts k args 5+PA194Site42SecondTo14.lefts k args 5,F ones ![e 5+1,tail]]] at h14
  rw [ha,hq] at h14
  have h16 := PA194FourteenOddTo16.fourteenOddTo16 a u
  dsimp only at h16
  have h2 := PA194SixteenTwoRuns.modelSixteenTwoRuns (e 4) (e 3) x3 r
  dsimp only at h2
  change F PA194Stepper.stepper ![(e 4+1)+((e 3+1)+1),F pairCode ![modelNumeral M 16,F pairCode ![
    F halfCode (fun _ => a),F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x3),F parityCode (fun _ => x3)+(w2+w2)+(w2+w2)]] at h2
  have h3 := PA194Site35MarkerReturnNext.modelMarkerReturnNext (e 2) x2 w2
  have h4 := PA194Site35MarkerReturnNext.modelMarkerReturnNext (e 1) x1 w3
  have h5 := PA194Site35MarkerReturnNext.modelMarkerReturnNext (e 0) b w4
  have hgap := PA194Site35MarkerReturnNext.modelMarkerReturnNext (k+1) (modelNumeral M 202) w5
  dsimp only at h3 h4 h5 hgap
  have hb : b = F ones ![(k+1)+1,modelNumeral M 404] := by
    change (F ones ![k,modelNumeral M 404]+F ones ![k,modelNumeral M 404]+1)+(F ones ![k,modelNumeral M 404]+F ones ![k,modelNumeral M 404]+1)+1 = _
    change _ = F ones ![F addCode ![k+1,F oneCode Fin.elim0],_]
    rw [modelAddOne,modelOnesSucc]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],_]+_+1
    rw [modelAddOne,modelOnesSucc]
    change _ = _ + F ones ![F addCode ![k,F oneCode Fin.elim0],_]+1
    rw [modelAddOne,modelOnesSucc]
  have h404 : modelNumeral M 202+modelNumeral M 202 = modelNumeral M 404 := by rw [←modelNumeralAdd]
  rw [h404,←hb] at hgap
  have h202 : modelNumeral M 202 = modelNumeral M 101+modelNumeral M 101 := by rw [←modelNumeralAdd]
  rw [h202,(modelDouble (modelNumeral M 101)).1,(modelDouble (modelNumeral M 101)).2,zero_add] at hgap
  change F PA194Stepper.stepper ![(e 2+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x3),F parityCode (fun _ => x3)+(w2+w2)+(w2+w2)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x2),F parityCode (fun _ => x2)+(w3+w3)+(w3+w3)]] at h3
  change F PA194Stepper.stepper ![(e 1+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x2),F parityCode (fun _ => x2)+(w3+w3)+(w3+w3)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x1),F parityCode (fun _ => x1)+(w4+w4)+(w4+w4)]] at h4
  change F PA194Stepper.stepper ![(e 0+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x1),F parityCode (fun _ => x1)+(w4+w4)+(w4+w4)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => b),F parityCode (fun _ => b)+(w5+w5)+(w5+w5)]] at h5
  change F PA194Stepper.stepper ![((k+1)+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => b),F parityCode (fun _ => b)+(w5+w5)+(w5+w5)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 101,(output k args+output k args)+(output k args+output k args)]] at hgap
  rw [h14,h16,h2,h3,h4,h5,hgap]
#print axioms to17
end models
end PA194Site42SecondTo17
