import PA194Site29ReturnFinalBlocks
import PA194Site29ReturnSixFromSelected
import PA194Site29ReturnSixFast
import PA194Site29ReturnNormalized
import PA194ReturnCell
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ReturnAllBlocks
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194OnesCommute BinaryTapeCodes TableDispatch PA194ReturnCell PA194OnesCommute PA194UnaryRuns PA194BinaryDouble PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem returnAllBlocks (ns : Fin 7 → M) (m k d t : M) :
    let A := F ones ![k,(d+d)+(d+d)]
    let A1 := A+A+1
    let z := F ones ![m,(A1+A1)+(A1+A1)+1]
    let a0 := F ones ![ns 0,(z+z)+(z+z)+1]
    let a1 := F ones ![ns 1,(a0+a0)+(a0+a0)+1]
    let a2 := F ones ![ns 2,(a1+a1)+(a1+a1)+1]
    let a3 := F ones ![ns 3,(a2+a2)+(a2+a2)+1]
    let a4 := F ones ![ns 4,(a3+a3)+(a3+a3)+1]
    let a5 := F ones ![ns 5,(a4+a4)+(a4+a4)+1]
    let selected := F ones ![ns 6,(a5+a5)+(a5+a5)+1]
    let r0 := t
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
                  F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => selected),F parityCode (fun _ => selected)+(r0+r0)+(r0+r0)]]]]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![d,(r9+r9)+(r9+r9)]] := by
  let A := F ones ![k,(d+d)+(d+d)]
  let A1 := A+A+1
  let z := F ones ![m,(A1+A1)+(A1+A1)+1]
  let r0 := t
  let r1 := F ones ![ns 6,(1 : M)+(r0+r0)+(r0+r0)]
  let r2 := F ones ![ns 5,(1 : M)+(r1+r1)+(r1+r1)]
  let r3 := F ones ![ns 4,(1 : M)+(r2+r2)+(r2+r2)]
  let r4 := F ones ![ns 3,(1 : M)+(r3+r3)+(r3+r3)]
  let r5 := F ones ![ns 2,(1 : M)+(r4+r4)+(r4+r4)]
  let r6 := F ones ![ns 1,(1 : M)+(r5+r5)+(r5+r5)]
  let outer : M → M := fun x => F PA194Stepper.stepper ![(k+1)+1,
    F PA194Stepper.stepper ![(m+1)+1,F PA194Stepper.stepper ![(ns 0+1)+1,x]]]
  have first := PA194Site29ReturnSixFromSelected.sixFromSelected ns z t
  dsimp only at first
  have second := PA194Site29ReturnFinalBlocks.remainingReturn (ns 0) m k d r6
  dsimp only at second
  exact (congrArg outer first).trans second
#print axioms returnAllBlocks
end models
end PA194Site29ReturnAllBlocks
