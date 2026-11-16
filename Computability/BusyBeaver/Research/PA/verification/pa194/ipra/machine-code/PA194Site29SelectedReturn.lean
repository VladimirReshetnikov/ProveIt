import PA194Site29SeedTailRoundTrip
import PA194Site29ReturnNext
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29SelectedReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194RegisterFile PA194UnaryRuns PA194Site28SeedTail PA194Site28CarryCodes PA194Site28CarryFile PA194StartupSourceFrame PA194BinaryDouble PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem selectedReturn (n a spare : M) :
    let base := (a+a)+(a+a)+1
    let marked := F ones ![n+1,base]
    let seed := F block ![(1 : M),modelNumeral M seedTail]
    let e := PA194Site29SeedTailRoundTrip.ext spare
    let vv := e ⟨26,by decide⟩
    let ss := ((1 : M)+1)+1
    let qq := ss+ss
    let ww := F ones ![vv,(1 : M)+qq+qq]
    let tt := ww+ww
    let vals : Fin 27 → M := fun i => e i.castSucc
    let out := F (PA194ReturnFile.returnCode 26) (Fin.cases tt vals)
    let right := F ones ![n+1,(1 : M)+out+out]
    F PA194Stepper.stepper ![((n+1)+1)+1,
      F PA194Stepper.stepper ![F (PA194CarryFile.costCode 26) vals,
        F PA194Stepper.stepper ![modelNumeral M 2+((vv+1)+1),
          F PA194Stepper.stepper ![modelNumeral M 3,
            F PA194Stepper.stepper ![(1 : M)+(vv+1),
              F PA194Stepper.stepper ![F (timeCode 26) e,
                F pairCode ![modelNumeral M 3,F pairCode ![marked,F ones ![spare+1,seed]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => a),
      F parityCode (fun _ => a)+(right+right)+(right+right)]] := by
  dsimp only
  let base := (a+a)+(a+a)+1
  let marked := F ones ![n+1,base]
  let e := PA194Site29SeedTailRoundTrip.ext spare
  let vv := e ⟨26,by decide⟩
  let ss := ((1 : M)+1)+1
  let qq := ss+ss
  let ww := F ones ![vv,(1 : M)+qq+qq]
  let tt := ww+ww
  let vals : Fin 27 → M := fun i => e i.castSucc
  let out := F (PA194ReturnFile.returnCode 26) (Fin.cases tt vals)
  have hm : marked = F ones ![n,base]+F ones ![n,base]+1 := by
    dsimp only [marked]
    rw [show n+1 = F Code.succ (fun _ => n) from modelAddOne _,modelOnesSucc]
  have ho : F parityCode (fun _ => marked) = (1 : M) := by rw [hm,(modelOdd _).1]
  have hh : F halfCode (fun _ => marked) = F ones ![n,base] := by rw [hm,(modelOdd _).2]
  have carry := PA194Site29SeedTailRoundTrip.seedTailRoundTrip spare marked ho
  dsimp only at carry
  rw [hh] at carry
  have ret := PA194Site29ReturnNext.returnNext n a out
  dsimp only at ret
  rw [carry,ret]
#print axioms selectedReturn
end models
end PA194Site29SelectedReturn
