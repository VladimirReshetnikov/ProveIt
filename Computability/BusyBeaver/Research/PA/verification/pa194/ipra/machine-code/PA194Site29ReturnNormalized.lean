import PA194Site29ReturnNext
import PA194ReturnCell
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ReturnNormalized
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
theorem returnPrevious (n m a t : M) :
    let z := F ones ![m,(a+a)+(a+a)+1]
    let right := F ones ![n,(1 : M)+(t+t)+(t+t)]
    F PA194Stepper.stepper ![(n+1)+1,F pairCode ![modelNumeral M 7,
      F pairCode ![F ones ![n,z+z],(1 : M)+(t+t)+(t+t)]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F ones ![m,a+a],
      (1 : M)+(right+right)+(right+right)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := PA194Site29ReturnNext.returnPrevious n m a (t+t)
  dsimp only at h ⊢
  simpa only [add_assoc,add_comm,add_left_comm] using h
#print axioms returnPrevious
end models
end PA194Site29ReturnNormalized
