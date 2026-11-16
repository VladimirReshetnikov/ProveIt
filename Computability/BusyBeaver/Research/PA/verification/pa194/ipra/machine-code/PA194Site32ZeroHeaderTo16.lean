import PA194Site32ZeroHeaderShape
import PA194FirstThreeBlankTailTo16
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site32ZeroHeaderTo16
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194ZeroRuns PA194ZerosDouble PA194Site32ZeroHeaderShape PA194FirstThreeBlankTailTo16 BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem from14To16 (k a p : M) :
    let l := a+a+1
    let n := (((k+1)+1)+1)+1
    let left := F zeros ![k+1,F zeros ![modelNumeral M 5,l]+F zeros ![modelNumeral M 5,l]]
    let z := F zeros ![n,(1 : M)+(p+p)+(p+p)]
    let r := (z+z)+(z+z)
    F PA194Stepper.stepper ![((1 : M)+n)+modelNumeral M 3,
      F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => left),F parityCode (fun _ => left)+(p+p)+(p+p)]]] =
    F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a),F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]] := by
  dsimp only
  let l := a+a+1
  let n := (((k+1)+1)+1)+1
  let y := F zeros ![n,l+l]
  have hleft := leftShape k l
  dsimp only at hleft
  rw [hleft,(modelDouble (y+y)).1,(modelDouble (y+y)).2,zero_add]
  exact header14To16 n a p
#print axioms from14To16
end models
end PA194Site32ZeroHeaderTo16
