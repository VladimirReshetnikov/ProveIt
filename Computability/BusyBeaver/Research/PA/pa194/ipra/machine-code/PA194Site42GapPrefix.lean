import PA194Site30Jump
import PA194Site32PositivePath
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace PA194Site42GapPrefix
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194LeftRows PA194LeftOneRows PA194LeftOneWriteOne PA194RightRows PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
theorem row0 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 202,modelWord [false] x]]) =
    F pairCode ![modelNumeral M 36,F pairCode ![modelNumeral M 101,modelWord [false,false] x]] := by
  let y := modelWord [] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 202,y+y]]) =
    F pairCode ![modelNumeral M 36,F pairCode ![modelNumeral M 101,(y+y)+(y+y)]]
  have h := leftZero 30 36 (by decide) (by decide +kernel) (modelNumeral M 202) y
  have hn : modelNumeral M 202 = modelNumeral M 101+modelNumeral M 101 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 202) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 101)).1]
  have hh : F halfCode (fun _ => modelNumeral M 202) = modelNumeral M 101 := by rw [hn,(modelDouble (modelNumeral M 101)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row1 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 36,F pairCode ![modelNumeral M 101,modelWord [false,false] x]]) =
    F pairCode ![modelNumeral M 48,F pairCode ![modelNumeral M 202,modelWord [false] x]] := by
  let y := modelWord [false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 36,F pairCode ![modelNumeral M 101,y+y]]) =
    F pairCode ![modelNumeral M 48,F pairCode ![modelNumeral M 202,y]]
  have h := rightZero 36 0 48 (by decide) (by decide +kernel) (modelNumeral M 101) y
  have hn : modelNumeral M 101+modelNumeral M 101+modelNumeral M 0 = modelNumeral M 202 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row2 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 48,F pairCode ![modelNumeral M 202,modelWord [false] x]]) =
    F pairCode ![modelNumeral M 59,F pairCode ![modelNumeral M 404,modelWord [] x]] := by
  let y := modelWord [] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 48,F pairCode ![modelNumeral M 202,y+y]]) =
    F pairCode ![modelNumeral M 59,F pairCode ![modelNumeral M 404,y]]
  have h := rightZero 48 0 59 (by decide) (by decide +kernel) (modelNumeral M 202) y
  have hn : modelNumeral M 202+modelNumeral M 202+modelNumeral M 0 = modelNumeral M 404 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem prefixWord (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 202,modelWord [false] x]]] =
    F pairCode ![modelNumeral M 59,F pairCode ![modelNumeral M 404,modelWord [] x]] := by
  rw [PA194Site30Jump.standardRunCorrect]
  simp only [PA194Site30Jump.standardRun]
  rw [row0,row1,row2]
#print axioms prefixWord
end models
end PA194Site42GapPrefix
