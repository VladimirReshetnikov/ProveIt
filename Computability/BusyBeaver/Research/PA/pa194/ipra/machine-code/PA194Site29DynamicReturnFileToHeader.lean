import PA194Site29DynamicSelectedAndSix
import PA194Site29ReturnAllBlocks
import PA194Site29SelectedAndSix
import PA194Site29ReturnSixFromSelected
import PA194Site29SelectedReturn
import PA194Site29SeedTailRoundTrip
import PA194Site29ReturnNext
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29DynamicReturnFileToHeader
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194RegisterFile PA194UnaryRuns PA194Site28SeedTail PA194Site28CarryCodes PA194Site28CarryFile PA194StartupSourceFrame PA194BinaryDouble PA194OneSpareReturn PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem returnFileToHeader (ns : Fin 7 → M) (m k d n spare count : M) :
    let A := F ones ![k,(d+d)+(d+d)]
    let A1 := A+A+1
    let z := F ones ![m,(A1+A1)+(A1+A1)+1]
    let a0 := F ones ![ns 0,(z+z)+(z+z)+1]
    let a1 := F ones ![ns 1,(a0+a0)+(a0+a0)+1]
    let a2 := F ones ![ns 2,(a1+a1)+(a1+a1)+1]
    let a3 := F ones ![ns 3,(a2+a2)+(a2+a2)+1]
    let a4 := F ones ![ns 4,(a3+a3)+(a3+a3)+1]
    let a5 := F ones ![ns 5,(a4+a4)+(a4+a4)+1]
    let a := F ones ![ns 6,(a5+a5)+(a5+a5)+1]
    let base := (a+a)+(a+a)+1
    let marked := F ones ![n+1,base]
    let seed := F repeatOutput ![count,(0 : M)]
    let out := F block ![spare,F repeatOutput ![F Code.succ (fun _ => count),(0 : M)]]
    let right := F ones ![n+1,(1 : M)+out+out]
    let r0 := right
    let r1 := F ones ![ns 6,(1 : M)+(r0+r0)+(r0+r0)]
    let r2 := F ones ![ns 5,(1 : M)+(r1+r1)+(r1+r1)]
    let r3 := F ones ![ns 4,(1 : M)+(r2+r2)+(r2+r2)]
    let r4 := F ones ![ns 3,(1 : M)+(r3+r3)+(r3+r3)]
    let r5 := F ones ![ns 2,(1 : M)+(r4+r4)+(r4+r4)]
    let r6 := F ones ![ns 1,(1 : M)+(r5+r5)+(r5+r5)]
    let r7 := F ones ![ns 0,(1 : M)+(r6+r6)+(r6+r6)]
    let r8 := F ones ![m,(1 : M)+(r7+r7)+(r7+r7)]
    let r9 := F ones ![k,(1 : M)+(r8+r8)+(r8+r8)]
    F PA194Stepper.stepper ![(k+1)+1,
      F PA194Stepper.stepper ![(m+1)+1,
        F PA194Stepper.stepper ![(ns 0+1)+1,
          F PA194Stepper.stepper ![(ns 1+1)+1,
      F PA194Stepper.stepper ![(ns 2+1)+1,
        F PA194Stepper.stepper ![(ns 3+1)+1,
          F PA194Stepper.stepper ![(ns 4+1)+1,
            F PA194Stepper.stepper ![(ns 5+1)+1,
              F PA194Stepper.stepper ![(ns 6+1)+1,
      F PA194Stepper.stepper ![((n+1)+1)+1,
      F PA194Stepper.stepper ![(spare+1)+1,
        F PA194Stepper.stepper ![(count+count)+count,
          F PA194Stepper.stepper ![modelNumeral M 2,
            F PA194Stepper.stepper ![modelNumeral M 3,
              F PA194Stepper.stepper ![(count+count)+count,
                F PA194Stepper.stepper ![(1 : M)+(spare+1),
                F pairCode ![modelNumeral M 3,F pairCode ![marked,F ones ![spare+1,seed]]]]]]]]]]]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![d,(r9+r9)+(r9+r9)]] := by
  let A := F ones ![k,(d+d)+(d+d)]
  let A1 := A+A+1
  let z := F ones ![m,(A1+A1)+(A1+A1)+1]
  let a0 := F ones ![ns 0,(z+z)+(z+z)+1]
  let a1 := F ones ![ns 1,(a0+a0)+(a0+a0)+1]
  let a2 := F ones ![ns 2,(a1+a1)+(a1+a1)+1]
  let a3 := F ones ![ns 3,(a2+a2)+(a2+a2)+1]
  let a4 := F ones ![ns 4,(a3+a3)+(a3+a3)+1]
  let a5 := F ones ![ns 5,(a4+a4)+(a4+a4)+1]
  let a := F ones ![ns 6,(a5+a5)+(a5+a5)+1]
  let out := F block ![spare,F repeatOutput ![F Code.succ (fun _ => count),(0 : M)]]
  let right := F ones ![n+1,(1 : M)+out+out]
  let outer : M → M := fun x => F PA194Stepper.stepper ![(k+1)+1,
    F PA194Stepper.stepper ![(m+1)+1,F PA194Stepper.stepper ![(ns 0+1)+1,x]]]
  have first := PA194Site29DynamicSelectedAndSix.selectedAndSix ns z n spare count
  dsimp only at first
  let r1 := F ones ![ns 6,(1 : M)+(right+right)+(right+right)]
  let r2 := F ones ![ns 5,(1 : M)+(r1+r1)+(r1+r1)]
  let r3 := F ones ![ns 4,(1 : M)+(r2+r2)+(r2+r2)]
  let r4 := F ones ![ns 3,(1 : M)+(r3+r3)+(r3+r3)]
  let r5 := F ones ![ns 2,(1 : M)+(r4+r4)+(r4+r4)]
  let r6 := F ones ![ns 1,(1 : M)+(r5+r5)+(r5+r5)]
  have second := PA194Site29ReturnFinalBlocks.remainingReturn (ns 0) m k d r6
  dsimp only at second
  exact (congrArg outer first).trans second
#print axioms returnFileToHeader
end models
end PA194Site29DynamicReturnFileToHeader
