import PA194OneSpareRoundTrip
import PA194OneSpareIdentities
import PA194Site28IncrementWrite
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site31DynamicTail
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194OneSpareIterate PA194OneSpareReturn PA194OneSpareRoundTrip PA194OneSpareIdentities PA194UnaryRuns PA194BinaryDouble PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

/-- The carry traverses and returns through a model-valued count of one-valued
spares after the fixed register file. -/
theorem tailRoundTrip (n l : M) :
    let six := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let out := F repeatOutput ![n,six]
    F PA194Stepper.stepper ![(n+n)+n,
      F PA194Stepper.stepper ![modelNumeral M 2,
        F PA194Stepper.stepper ![modelNumeral M 3,
          F PA194Stepper.stepper ![(n+n)+n,
            F PA194Stepper.stepper ![(1 : M),F pairCode ![(1 : M),
              F pairCode ![l,F repeatOutput ![n,(0 : M)]]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![l,out+out+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let b := F repeatBlock ![n,(0 : M)]
  have hs := PA194Site28IncrementWrite.incrementWrite (0 : M) l b
  rw [modelOnesZero,zero_add] at hs
  have ho : F ones ![(1 : M),l] = l+l+1 := by
    rw [←modelNumeralOne]
    change F ones ![F Code.succ (fun _ => modelNumeral M 0),l] = _
    rw [modelOnesSucc,show modelNumeral M 0 = (0 : M) from rfl,modelOnesZero,modelNumeralOne]
  rw [ho] at hs
  have hm := PA194OneSpareRoundTrip.roundTrip n (l+l+1) ((modelOdd l).1)
  dsimp only at hm
  rw [(modelOdd l).2] at hm
  have hi : F repeatOutput ![n,(0 : M)] = b+b := modelSuffixRelation n
  rw [hi,hs,hm]
#print axioms tailRoundTrip
end models
end PA194Site31DynamicTail
