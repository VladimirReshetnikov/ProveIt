import PA194FirstThreeBlankTailTo16
import PA194ZerosDouble
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194ZeroReturnTo16
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open TableDispatch PA194FirstThreeBlankTailTo16 PA194ZeroRuns PA194ZerosDouble
open PA194HeaderController PA194BinaryDouble BinaryTapeCodes PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem from14To16 (k a p : M) :
    let l := a+a+1
    let lzero := F zeros ![modelNumeral M 2,l]
    let left := F zeros ![k+1,lzero+lzero]
    let z := F zeros ![k+1,(1 : M)+(p+p)+(p+p)]
    let r := (z+z)+(z+z)
    F PA194Stepper.stepper ![((1 : M)+(k+1))+modelNumeral M 3,
      F pairCode ![modelNumeral M 14,F pairCode ![F halfCode (fun _ => left),F parityCode (fun _ => left)+(p+p)+(p+p)]]] =
    F pairCode ![modelNumeral M 16,F pairCode ![F halfCode (fun _ => a),F parityCode (fun _ => a)+(1+1)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  let l := a+a+1
  let x := l+l
  let y := F zeros ![k+1,x]
  let z := F zeros ![k,l]
  have hy : y = (z+z)+(z+z) := by
    dsimp [y,x]
    rw [show k+1 = F Code.succ (fun _ => k) from modelAddOne k,modelZerosSucc,modelZerosDouble]
  have hleft : F zeros ![k+1,F zeros ![modelNumeral M 2,l]+F zeros ![modelNumeral M 2,l]] = (y+y)+(y+y) := by
    rw [show k+1 = F Code.succ (fun _ => k) from modelAddOne k,modelZerosSucc,zerosTwo]
    rw [modelZerosDouble,modelZerosDouble,modelZerosDouble,hy]
  rw [hleft,(modelDouble (y+y)).1,(modelDouble (y+y)).2,zero_add]
  exact header14To16 (k+1) a p
#print axioms from14To16
end models
end PA194ZeroReturnTo16
