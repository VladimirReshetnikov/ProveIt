import PA194Site29ReturnNormalized
import PA194ReturnCell
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ReturnSixFast
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194ReturnCell PA194OnesCommute PA194UnaryRuns PA194BinaryDouble PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem returnSix (ns : Fin 7 → M) (z t : M) :
    let a0 := F ones ![ns 0,(z+z)+(z+z)+1]
    let a1 := F ones ![ns 1,(a0+a0)+(a0+a0)+1]
    let a2 := F ones ![ns 2,(a1+a1)+(a1+a1)+1]
    let a3 := F ones ![ns 3,(a2+a2)+(a2+a2)+1]
    let a4 := F ones ![ns 4,(a3+a3)+(a3+a3)+1]
    let a5 := F ones ![ns 5,(a4+a4)+(a4+a4)+1]
    let r0 := t
    let r1 := F ones ![ns 6,(1 : M)+(r0+r0)+(r0+r0)]
    let r2 := F ones ![ns 5,(1 : M)+(r1+r1)+(r1+r1)]
    let r3 := F ones ![ns 4,(1 : M)+(r2+r2)+(r2+r2)]
    let r4 := F ones ![ns 3,(1 : M)+(r3+r3)+(r3+r3)]
    let r5 := F ones ![ns 2,(1 : M)+(r4+r4)+(r4+r4)]
    let r6 := F ones ![ns 1,(1 : M)+(r5+r5)+(r5+r5)]
    F PA194Stepper.stepper ![(ns 1+1)+1,
        F PA194Stepper.stepper ![(ns 2+1)+1,
          F PA194Stepper.stepper ![(ns 3+1)+1,
            F PA194Stepper.stepper ![(ns 4+1)+1,
              F PA194Stepper.stepper ![(ns 5+1)+1,
                F PA194Stepper.stepper ![(ns 6+1)+1,
                  F pairCode ![modelNumeral M 7,F pairCode ![F ones ![ns 6,a5+a5],(1 : M)+(r0+r0)+(r0+r0)]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F ones ![ns 0,z+z],(1 : M)+(r6+r6)+(r6+r6)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let a0 := F ones ![ns 0,(z+z)+(z+z)+1]
  let a1 := F ones ![ns 1,(a0+a0)+(a0+a0)+1]
  let a2 := F ones ![ns 2,(a1+a1)+(a1+a1)+1]
  let a3 := F ones ![ns 3,(a2+a2)+(a2+a2)+1]
  let a4 := F ones ![ns 4,(a3+a3)+(a3+a3)+1]
  let a5 := F ones ![ns 5,(a4+a4)+(a4+a4)+1]
  let r0 := t
  let r1 := F ones ![ns 6,(1 : M)+(r0+r0)+(r0+r0)]
  let r2 := F ones ![ns 5,(1 : M)+(r1+r1)+(r1+r1)]
  let r3 := F ones ![ns 4,(1 : M)+(r2+r2)+(r2+r2)]
  let r4 := F ones ![ns 3,(1 : M)+(r3+r3)+(r3+r3)]
  let r5 := F ones ![ns 2,(1 : M)+(r4+r4)+(r4+r4)]
  let r6 := F ones ![ns 1,(1 : M)+(r5+r5)+(r5+r5)]
  have h1 := PA194Site29ReturnNormalized.returnPrevious (ns 6) (ns 5) a4 r0
  dsimp only at h1
  have h2 := PA194Site29ReturnNormalized.returnPrevious (ns 5) (ns 4) a3 r1
  dsimp only at h2
  have h3 := PA194Site29ReturnNormalized.returnPrevious (ns 4) (ns 3) a2 r2
  dsimp only at h3
  have h4 := PA194Site29ReturnNormalized.returnPrevious (ns 3) (ns 2) a1 r3
  dsimp only at h4
  have h5 := PA194Site29ReturnNormalized.returnPrevious (ns 2) (ns 1) a0 r4
  dsimp only at h5
  have h6 := PA194Site29ReturnNormalized.returnPrevious (ns 1) (ns 0) z r5
  dsimp only at h6
  rw [h1,h2,h3,h4,h5,h6]
#print axioms returnSix
end models
end PA194Site29ReturnSixFast
