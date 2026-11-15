import PA194ReturnCell
import PA194OnesCommute
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site29ReturnNext
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
theorem returnNext (n a t : M) :
    let left := F ones ![n,(a+a)+(a+a)+1]
    let right := F ones ![n+1,(1 : M)+t+t]
    F PA194Stepper.stepper ![((n+1)+1)+1,F pairCode ![modelNumeral M 7,
      F pairCode ![left,t+t+1]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => a),
      F parityCode (fun _ => a)+(right+right)+(right+right)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have hword : F ones ![n,(a+a)+(a+a)+1] = F ones ![n+1,a+a] := by
    rw [modelOnesCommute]
    change _ = F ones ![F addCode ![n,F oneCode Fin.elim0],a+a]
    rw [modelAddOne,modelOnesSucc]
  rw [hword]
  exact modelReturnCell (n+1) a t
theorem returnPrevious (n m a t : M) :
    let z := F ones ![m,(a+a)+(a+a)+1]
    let right := F ones ![n,(1 : M)+t+t]
    F PA194Stepper.stepper ![(n+1)+1,F pairCode ![modelNumeral M 7,
      F pairCode ![F ones ![n,z+z],t+t+1]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F ones ![m,a+a],
      (1 : M)+(right+right)+(right+right)]] := by
  dsimp only
  let z := F ones ![m,(a+a)+(a+a)+1]
  let zz := F ones ![m,a+a]
  have hz : z = zz+zz+1 := by
    dsimp only [z,zz]
    exact modelOnesCommute m (a+a)
  have hodd : F parityCode (fun _ => z) = (1 : M) := by rw [hz,(modelOdd zz).1]
  have hhalf : F halfCode (fun _ => z) = zz := by rw [hz,(modelOdd zz).2]
  have h := modelReturnCell n z t
  dsimp only at h
  rw [hodd,hhalf] at h
  exact h
#print axioms returnPrevious
#print axioms returnNext
end models
end PA194Site29ReturnNext
