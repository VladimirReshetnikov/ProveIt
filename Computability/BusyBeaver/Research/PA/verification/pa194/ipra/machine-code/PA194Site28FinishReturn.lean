import PA194Site28SeedRoundTrip
import PA194Site28ReturnSelected
import PA194Site28HeaderTo29
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site28FinishReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194Site28SeedRoundTrip PA194Site28ReturnSelected PA194Site28HeaderTo29 PA194Site28CarryFile PA194Site28ReturnCarry PA194RegisterPermutation PA194RegisterFile PA194ReturnFile PA194CarryFile PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194StateOne PRAModelIOpenPairing BinaryTapeCodes
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
def headerLeft : M :=
  let a0 := (1 : M)+(1 : M)+1
  let a1 := a0+a0
  let a2 := a1+a1
  let a3 := a2+a2
  let a4 := a3+a3+1
  let a5 := a4+a4
  let a6 := a5+a5+1
  a6+a6

def initialMark (k : M) (args : Fin 11 → M) : M :=
  let l := headerLeft (M := M)
  let d0 := F ones ![k,(l+l)+(l+l)]
  let d1 := d0+d0+1
  let d2 := d1+d1
  let d3 := d2+d2+1
  let d4 := F ones ![args 2,d3]
  let left := (d4+d4)+(d4+d4)+1
  F ones ![args 8+1,left]

def rest (args : Fin 11 → M) : Fin 9 → M := fun i => physicalArgs args ⟨i.val+2,by omega⟩

theorem marked_eq (k : M) (args : Fin 11 → M) :
    marked k args = carryLeft 7 (initialMark k args) (rest args) := by rfl

theorem initialMarkOdd (k : M) (args : Fin 11 → M) :
    F parityCode (fun _ => initialMark k args) = (1 : M) := by
  let l := headerLeft (M := M)
  let d0 := F ones ![k,(l+l)+(l+l)]
  let d1 := d0+d0+1
  let d2 := d1+d1
  let d3 := d2+d2+1
  let d4 := F ones ![args 2,d3]
  let left := (d4+d4)+(d4+d4)+1
  change F parityCode (fun _ => F ones ![args 8+1,left]) = (1 : M)
  have hs : F ones ![args 8+1,left] = F ones ![args 8,left]+F ones ![args 8,left]+1 := by
    change F ones ![F addCode ![args 8,F oneCode Fin.elim0],_] = _
    rw [modelAddOne,modelOnesSucc]
  rw [hs,(modelOdd _).1]

theorem finishReturn (k : M) (args : Fin 11 → M) (tail : M) :
    let l := headerLeft (M := M)
    let base := initialMark k args
    let es := rest args
    let vals : Fin 8 → M := fun i => es i.castSucc
    let out := F (PA194ReturnFile.returnCode 7) (Fin.cases tail vals)
    let w1 := F ones ![args 8+1,(1 : M)+out+out]
    let t1 := w1+w1
    let p := F ones ![args 2,(1 : M)+t1+t1]
    let w2 := F ones ![args 2,(1 : M)+t1+t1]
    let t2 := w2+w2
    let w3 := F ones ![k,(1 : M)+t2+t2]
    let rc := modelNumeral M 4+(((modelNumeral M 5+modelNumeral M 6)+modelNumeral M 2)+1)
    F PA194Stepper.stepper ![modelNumeral M 2+(modelNumeral M 3+rc),
      F PA194Stepper.stepper ![(1 : M),
        F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
          F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
            F PA194Stepper.stepper ![modelNumeral M 2,
              F PA194Stepper.stepper ![(k+1)+1,
                F PA194Stepper.stepper ![((args 2)+1)+1,
                  F PA194Stepper.stepper ![((args 8+1)+1)+1,
                    F PA194Stepper.stepper ![F (PA194CarryFile.costCode 7) vals,
                      F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => marked k args),tail+tail+1]]]]]]]]]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),
      PA194Path27Header.modelWord (PA194SourceProgram.path 29) (F zeros ![k+1,(1 : M)+(p+p)+(p+p)])]] := by
  let es := rest args
  let base := initialMark k args
  let vals : Fin 8 → M := fun i => es i.castSucc
  let out := F (PA194ReturnFile.returnCode 7) (Fin.cases tail vals)
  let w1 := F ones ![args 8+1,(1 : M)+out+out]
  let t1 := w1+w1
  let p := F ones ![args 2,(1 : M)+t1+t1]
  have hb := PA194Site28ReturnCarry.returnCarry (M := M) 7 es base tail (initialMarkOdd k args)
  rw [←marked_eq] at hb
  dsimp only at hb
  have hs := PA194Site28ReturnSelected.returnSelected (M := M) (args 8) (args 2) k (headerLeft (M := M)) out
  dsimp only at hs
  let w := F ones ![k,(1 : M)+(p+p)+(p+p)]
  change F PA194Stepper.stepper ![(k+1)+1,
    F PA194Stepper.stepper ![((args 2)+1)+1,
      F PA194Stepper.stepper ![((args 8+1)+1)+1,
        F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => base),out+out+1]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![headerLeft (M := M),(w+w)+(w+w)]] at hs
  have hh := PA194Site28HeaderTo29.headerTo29 (M := M) k p
  dsimp only at hh
  dsimp only
  rw [hb]
  change F PA194Stepper.stepper ![modelNumeral M 2+(modelNumeral M 3+_),
    F PA194Stepper.stepper ![(1 : M),
      F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
        F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![(k+1)+1,
              F PA194Stepper.stepper ![((args 2)+1)+1,
                F PA194Stepper.stepper ![((args 8+1)+1)+1,
                  F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => base),out+out+1]]]]]]]]]] = _
  rw [hs]
  change F PA194Stepper.stepper ![modelNumeral M 2+(modelNumeral M 3+_),
    F PA194Stepper.stepper ![(1 : M),
      F PA194Stepper.stepper ![((1 : M)+k)+modelNumeral M 3,
        F PA194Stepper.stepper ![((modelNumeral M 2+1)+k)+1,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F pairCode ![modelNumeral M 7,F pairCode ![headerLeft (M := M),(w+w)+(w+w)]]]]]]] = _
  exact hh
#print axioms marked_eq
#print axioms initialMarkOdd
#print axioms finishReturn
end models
end PA194Site28FinishReturn
