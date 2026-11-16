import PA194Site48SecondTo14
import PA194FourteenOddTo16
import PA194Site35SixteenSixRuns
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site48SecondTo17
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
  let tail := F (fileCode 5) (fun i => e ⟨i.val+5,by omega⟩)
  let u := F ones ![e 4,tail]
  let r := (u+u)+(u+u)
  let w1 := F ones ![e 3,(1 : M)+r+r]
  let w2 := F ones ![e 2,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![e 1,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![e 0,(1 : M)+(w3+w3)+(w3+w3)]
  F ones ![k+1,(1 : M)+(w4+w4)+(w4+w4)]
noncomputable def clock14 (k : M) (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  let n := (k+1)+1
  let c := ((e 0+1)+1)+((e 1+1)+1)
  let d := ((e 2+1)+1)+((e 3+1)+1)
  F addCode ![F addCode ![F addCode ![F addCode ![PA194Site48SecondTo95.firstClock k,modelNumeral M 8],n+1],c],d]
noncomputable def fourCost (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  (((e 3+1)+((e 2+1)+1))+((e 1+1)+1))+((e 0+1)+1)

theorem to17 (k : M) (args : Fin 11 → M) :
    let out := output k args
    F PA194Stepper.stepper ![((k+1)+1)+1,
      F PA194Stepper.stepper ![fourCost args,
        F PA194Stepper.stepper ![modelNumeral M 3,
          F PA194Stepper.stepper ![clock14 k args,
            PA194SourceSite31Physical.physicalFrame 48 ((k+1)+1) args]]]] =
      F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 26,(out+out)+(out+out)]] := by
  dsimp only
  let e := physicalArgs args
  let tail := F (fileCode 5) (fun i => e ⟨i.val+5,by omega⟩)
  let u := F ones ![e 4,tail]
  let r := (u+u)+(u+u)
  let a0 := F ones ![k,modelNumeral M 104]
  let b := a0+a0+1+(a0+a0+1)+1
  let x1 := F ones ![e 0+1,b+b]
  let x2 := F ones ![e 1+1,x1+x1]
  let x3 := F ones ![e 2+1,x2+x2]
  let a := F ones ![e 3,x3+x3]
  let w1 := F ones ![e 3,(1 : M)+r+r]
  let w2 := F ones ![e 2,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![e 1,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![e 0,(1 : M)+(w3+w3)+(w3+w3)]
  have ha : F ones ![e 3+1,x3+x3] = a+a+1 := by
    change F ones ![F addCode ![e 3,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hq : F ones ![e 4+1,tail] = u+u+1 := by
    change F ones ![F addCode ![e 4,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h14 := PA194Site48SecondTo14.to14 k args
  dsimp only at h14
  change _ = F pairCode ![modelNumeral M 14,F pairCode ![F ones ![e 3+1,x3+x3]+F ones ![e 3+1,x3+x3],F ones ![e 4+1,tail]]] at h14
  rw [ha,hq] at h14
  change F PA194Stepper.stepper ![clock14 k args,PA194SourceSite31Physical.physicalFrame 48 ((k+1)+1) args] =
    F pairCode ![modelNumeral M 14,F pairCode ![(a+a+1)+(a+a+1),u+u+1]] at h14
  have h16 := PA194FourteenOddTo16.fourteenOddTo16 a u
  dsimp only at h16
  have h2 := PA194SixteenTwoRuns.modelSixteenTwoRuns (e 3) (e 2) x2 r
  dsimp only at h2
  change F PA194Stepper.stepper ![(e 3+1)+((e 2+1)+1),F pairCode ![modelNumeral M 16,F pairCode ![
    F halfCode (fun _ => a),F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x2),F parityCode (fun _ => x2)+(w2+w2)+(w2+w2)]] at h2
  have h3 := PA194Site35MarkerReturnNext.modelMarkerReturnNext (e 1) x1 w2
  have h4 := PA194Site35MarkerReturnNext.modelMarkerReturnNext (e 0) b w3
  dsimp only at h3 h4
  change F PA194Stepper.stepper ![(e 1+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x2),F parityCode (fun _ => x2)+(w2+w2)+(w2+w2)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x1),F parityCode (fun _ => x1)+(w3+w3)+(w3+w3)]] at h3
  change F PA194Stepper.stepper ![(e 0+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x1),F parityCode (fun _ => x1)+(w3+w3)+(w3+w3)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => b),F parityCode (fun _ => b)+(w4+w4)+(w4+w4)]] at h4
  have hfour : F PA194Stepper.stepper ![fourCost args,F pairCode ![modelNumeral M 16,F pairCode ![
    F halfCode (fun _ => a),F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => b),F parityCode (fun _ => b)+(w4+w4)+(w4+w4)]] := by
    dsimp only [fourCost]
    change F PA194Stepper.stepper ![F addCode ![F addCode ![(e 3+1)+((e 2+1)+1),(e 1+1)+1],(e 0+1)+1],_] = _
    rw [PA194StepperCompose.modelStepperCompose,PA194StepperCompose.modelStepperCompose,h2,h3,h4]
  have hg := PA194Site35MarkerReturnNext.modelMarkerReturnNext (k+1) (modelNumeral M 52) w4
  dsimp only at hg
  have hb : b = F ones ![(k+1)+1,modelNumeral M 104] := by
    change (F ones ![k,modelNumeral M 104]+F ones ![k,modelNumeral M 104]+1)+(F ones ![k,modelNumeral M 104]+F ones ![k,modelNumeral M 104]+1)+1 = _
    change _ = F ones ![F addCode ![k+1,F oneCode Fin.elim0],_]
    rw [modelAddOne,modelOnesSucc]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],_]+_+1
    rw [modelAddOne,modelOnesSucc]
    change _ = _ + F ones ![F addCode ![k,F oneCode Fin.elim0],_]+1
    rw [modelAddOne,modelOnesSucc]
  have h412 : modelNumeral M 52+modelNumeral M 52 = modelNumeral M 104 := by rw [←modelNumeralAdd]
  rw [h412,←hb] at hg
  have h206 : modelNumeral M 52 = modelNumeral M 26+modelNumeral M 26 := by rw [←modelNumeralAdd]
  rw [h206,(modelDouble (modelNumeral M 26)).1,(modelDouble (modelNumeral M 26)).2,zero_add] at hg
  change F PA194Stepper.stepper ![((k+1)+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => b),F parityCode (fun _ => b)+(w4+w4)+(w4+w4)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 26,(output k args+output k args)+(output k args+output k args)]] at hg
  rw [h14,h16,hfour,hg]
#print axioms to17
end models
end PA194Site48SecondTo17
