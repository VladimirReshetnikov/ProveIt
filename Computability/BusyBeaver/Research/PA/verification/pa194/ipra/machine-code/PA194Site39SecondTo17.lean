import PA194Site39SecondTo14
import PA194FourteenOddTo16
import PA194Site35SixteenSixRuns
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site39SecondTo17
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
  let tail := F (fileCode 1) (fun i => e ⟨i.val+9,by omega⟩)
  let u := F ones ![e 8,tail]
  let r := (u+u)+(u+u)
  let w1 := F ones ![e 7,(1 : M)+r+r]
  let w2 := F ones ![e 6,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![e 5,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![e 4,(1 : M)+(w3+w3)+(w3+w3)]
  let w5 := F ones ![e 3,(1 : M)+(w4+w4)+(w4+w4)]
  let w6 := F ones ![e 2,(1 : M)+(w5+w5)+(w5+w5)]
  let w7 := F ones ![e 1,(1 : M)+(w6+w6)+(w6+w6)]
  let w8 := F ones ![e 0,(1 : M)+(w7+w7)+(w7+w7)]
  F ones ![k+1,(1 : M)+(w8+w8)+(w8+w8)]
noncomputable def sixCost (args : Fin 11 → M) : M :=
  let e := physicalArgs args
  (((((((e 7+1)+((e 6+1)+1))+((e 5+1)+1))+((e 4+1)+1))+((e 3+1)+1))+((e 2+1)+1)))

theorem to17 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let out := output k args
    F PA194Stepper.stepper ![((k+1)+1)+1,
      F PA194Stepper.stepper ![(e 0+1)+1,
        F PA194Stepper.stepper ![(e 1+1)+1,
          F PA194Stepper.stepper ![sixCost args,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![PA194Site39SecondTo14.clock k args,
                PA194SourceSite31Physical.physicalFrame 39 ((k+1)+1) args]]]]]] =
      F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 3227,(out+out)+(out+out)]] := by
  dsimp only
  let e := physicalArgs args
  let tail := F (fileCode 1) (fun i => e ⟨i.val+9,by omega⟩)
  let u := F ones ![e 8,tail]
  let r := (u+u)+(u+u)
  let b := PA194Site39SecondTo14.lefts k args 0
  let x1 := PA194Site39SecondTo14.lefts k args 1
  let x2 := PA194Site39SecondTo14.lefts k args 2
  let x7 := PA194Site39SecondTo14.lefts k args 7
  let a := F ones ![e 7,x7+x7]
  let w1 := F ones ![e 7,(1 : M)+r+r]
  let w2 := F ones ![e 6,(1 : M)+(w1+w1)+(w1+w1)]
  let w3 := F ones ![e 5,(1 : M)+(w2+w2)+(w2+w2)]
  let w4 := F ones ![e 4,(1 : M)+(w3+w3)+(w3+w3)]
  let w5 := F ones ![e 3,(1 : M)+(w4+w4)+(w4+w4)]
  let w6 := F ones ![e 2,(1 : M)+(w5+w5)+(w5+w5)]
  let w7 := F ones ![e 1,(1 : M)+(w6+w6)+(w6+w6)]
  let w8 := F ones ![e 0,(1 : M)+(w7+w7)+(w7+w7)]
  have ha : PA194Site39SecondTo14.lefts k args 8 = a+a+1 := by
    dsimp only [PA194Site39SecondTo14.lefts,a,x7]
    change F ones ![F addCode ![e 7,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
    rfl
  have hq : F ones ![e 8+1,tail] = u+u+1 := by
    dsimp only [u]
    change F ones ![F addCode ![e 8,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h14 := PA194Site39SecondTo14.to14 k args
  dsimp only at h14
  change _ = F pairCode ![modelNumeral M 14,F pairCode ![PA194Site39SecondTo14.lefts k args 8+PA194Site39SecondTo14.lefts k args 8,F ones ![e 8+1,tail]]] at h14
  rw [ha,hq] at h14
  have h16 := PA194FourteenOddTo16.fourteenOddTo16 a u
  dsimp only at h16
  have hs := PA194Site35SixteenSixRuns.modelSixteenSixRuns (e 2) (e 3) (e 4) (e 5) (e 6) (e 7) x2 r
  dsimp only at hs
  change F PA194Stepper.stepper ![sixCost args,F pairCode ![modelNumeral M 16,F pairCode ![
    F halfCode (fun _ => a),F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x2),F parityCode (fun _ => x2)+(w6+w6)+(w6+w6)]] at hs
  have h7 := PA194Site35MarkerReturnNext.modelMarkerReturnNext (e 1) x1 w6
  have h8 := PA194Site35MarkerReturnNext.modelMarkerReturnNext (e 0) b w7
  have h9 := PA194Site35MarkerReturnNext.modelMarkerReturnNext (k+1) (modelNumeral M 6454) w8
  dsimp only at h7 h8 h9
  have h6448 : modelNumeral M 6454+modelNumeral M 6454 = modelNumeral M 12908 := by rw [←modelNumeralAdd]
  rw [h6448] at h9
  have h3224 : modelNumeral M 6454 = modelNumeral M 3227+modelNumeral M 3227 := by rw [←modelNumeralAdd]
  rw [h3224,(modelDouble (modelNumeral M 3227)).1,(modelDouble (modelNumeral M 3227)).2,zero_add] at h9
  change F PA194Stepper.stepper ![(e 1+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x2),F parityCode (fun _ => x2)+(w6+w6)+(w6+w6)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x1),F parityCode (fun _ => x1)+(w7+w7)+(w7+w7)]] at h7
  change F PA194Stepper.stepper ![(e 0+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => x1),F parityCode (fun _ => x1)+(w7+w7)+(w7+w7)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => b),F parityCode (fun _ => b)+(w8+w8)+(w8+w8)]] at h8
  change F PA194Stepper.stepper ![((k+1)+1)+1,F pairCode ![modelNumeral M 17,F pairCode ![F halfCode (fun _ => b),F parityCode (fun _ => b)+(w8+w8)+(w8+w8)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 3227,(output k args+output k args)+(output k args+output k args)]] at h9
  rw [h14,h16,hs,h7,h8,h9]
#print axioms to17
end models
end PA194Site39SecondTo17
