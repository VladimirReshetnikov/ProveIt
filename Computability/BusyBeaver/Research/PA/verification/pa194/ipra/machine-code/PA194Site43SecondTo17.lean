import PA194Site43SecondTo14
import PA194FourteenOddTo16
import PA194Site35SixteenSixRuns
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
namespace PA194Site43SecondTo17
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
  let tail := F (fileCode 8) (fun i => e i.succ.succ)
  let u := F ones ![e 1,tail]
  let r := (u+u)+(u+u)
  let w := F ones ![e 0,(1 : M)+r+r]
  F ones ![k+1,(1 : M)+(w+w)+(w+w)]

theorem to17 (k : M) (args : Fin 11 → M) :
    let e := physicalArgs args
    let clock := F addCode ![F addCode ![F addCode ![PA194Site43SecondTo93.firstClock k,modelNumeral M 9],((k+1)+1)+1],(e 0+1)+1]
    let out := output k args
    F PA194Stepper.stepper ![(e 0+1)+(((k+1)+1)+1),
      F PA194Stepper.stepper ![modelNumeral M 3,
        F PA194Stepper.stepper ![clock,
          PA194SourceSite31Physical.physicalFrame 43 ((k+1)+1) args]]] =
      F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 203,(out+out)+(out+out)]] := by
  dsimp only
  let e := physicalArgs args
  let tail := F (fileCode 8) (fun i => e i.succ.succ)
  let u := F ones ![e 1,tail]
  let r := (u+u)+(u+u)
  let a0 := F ones ![k,modelNumeral M 812]
  let b := a0+a0+1+(a0+a0+1)+1
  let a := F ones ![e 0,b+b]
  let w := F ones ![e 0,(1 : M)+r+r]
  have ha : F ones ![e 0+1,b+b] = a+a+1 := by
    change F ones ![F addCode ![e 0,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have hq : F ones ![e 1+1,tail] = u+u+1 := by
    change F ones ![F addCode ![e 1,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  have h14 := PA194Site43SecondTo14.to14 k args
  dsimp only at h14
  change _ = F pairCode ![modelNumeral M 14,F pairCode ![F ones ![e 0+1,b+b]+F ones ![e 0+1,b+b],F ones ![e 1+1,tail]]] at h14
  rw [ha,hq] at h14
  have h16 := PA194FourteenOddTo16.fourteenOddTo16 a u
  dsimp only at h16
  have h2 := PA194SixteenTwoRuns.modelSixteenTwoRuns (e 0) (k+1) (modelNumeral M 406) r
  dsimp only at h2
  have hb : b = F ones ![(k+1)+1,modelNumeral M 812] := by
    change (F ones ![k,modelNumeral M 812]+F ones ![k,modelNumeral M 812]+1)+(F ones ![k,modelNumeral M 812]+F ones ![k,modelNumeral M 812]+1)+1 = _
    change _ = F ones ![F addCode ![k+1,F oneCode Fin.elim0],_]
    rw [modelAddOne,modelOnesSucc]
    change _ = F ones ![F addCode ![k,F oneCode Fin.elim0],_]+_+1
    rw [modelAddOne,modelOnesSucc]
    change _ = _ + F ones ![F addCode ![k,F oneCode Fin.elim0],_]+1
    rw [modelAddOne,modelOnesSucc]
  have h812 : modelNumeral M 406+modelNumeral M 406 = modelNumeral M 812 := by rw [←modelNumeralAdd]
  rw [h812,←hb] at h2
  have h406 : modelNumeral M 406 = modelNumeral M 203+modelNumeral M 203 := by rw [←modelNumeralAdd]
  rw [h406,(modelDouble (modelNumeral M 203)).1,(modelDouble (modelNumeral M 203)).2,zero_add] at h2
  change F PA194Stepper.stepper ![(e 0+1)+(((k+1)+1)+1),F pairCode ![modelNumeral M 16,F pairCode ![
    F halfCode (fun _ => a),F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 203,(output k args+output k args)+(output k args+output k args)]] at h2
  rw [h14,h16,h2]
#print axioms to17
end models
end PA194Site43SecondTo17
