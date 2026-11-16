import PA194Site32ZeroTo14
import PA194ZerosDouble
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace PA194Site32ZeroHeaderShape
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194ZeroRuns PA194ZerosDouble PA194Site32ZeroTo14 BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem leftShape (k l : M) :
    let n := (((k+1)+1)+1)+1
    let left := F zeros ![k+1,F zeros ![modelNumeral M 5,l]+F zeros ![modelNumeral M 5,l]]
    let y := F zeros ![n,l+l]
    left = (y+y)+(y+y) := by
  dsimp only
  have hs (n x : M) : F zeros ![n+1,x] = F zeros ![n,x]+F zeros ![n,x] := by
    change F zeros ![F addCode ![n,F oneCode Fin.elim0],x] = _
    rw [modelAddOne,modelZerosSucc]
  simp only [zerosFive,modelZerosDouble,hs]
#print axioms leftShape
end models
end PA194Site32ZeroHeaderShape
