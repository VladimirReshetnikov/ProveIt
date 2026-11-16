import PA194Site30Jump
import PA194Site32PositivePath
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace PA194Site0Prefix
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
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 25,F pairCode ![modelNumeral M 2,modelWord [false,false,false,false,false] x]] := by
  let y := modelWord [false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,y+y]]) =
    F pairCode ![modelNumeral M 25,F pairCode ![modelNumeral M 2,y]]
  have h := rightZero 24 0 25 (by decide) (by decide +kernel) (modelNumeral M 1) y
  have hn : modelNumeral M 1+modelNumeral M 1+modelNumeral M 0 = modelNumeral M 2 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row1 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 25,F pairCode ![modelNumeral M 2,modelWord [false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 27,F pairCode ![modelNumeral M 4,modelWord [false,false,false,false] x]] := by
  let y := modelWord [false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 25,F pairCode ![modelNumeral M 2,y+y]]) =
    F pairCode ![modelNumeral M 27,F pairCode ![modelNumeral M 4,y]]
  have h := rightZero 25 0 27 (by decide) (by decide +kernel) (modelNumeral M 2) y
  have hn : modelNumeral M 2+modelNumeral M 2+modelNumeral M 0 = modelNumeral M 4 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row2 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 27,F pairCode ![modelNumeral M 4,modelWord [false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 31,F pairCode ![modelNumeral M 8,modelWord [false,false,false] x]] := by
  let y := modelWord [false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 27,F pairCode ![modelNumeral M 4,y+y]]) =
    F pairCode ![modelNumeral M 31,F pairCode ![modelNumeral M 8,y]]
  have h := rightZero 27 0 31 (by decide) (by decide +kernel) (modelNumeral M 4) y
  have hn : modelNumeral M 4+modelNumeral M 4+modelNumeral M 0 = modelNumeral M 8 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row3 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 31,F pairCode ![modelNumeral M 8,modelWord [false,false,false] x]]) =
    F pairCode ![modelNumeral M 38,F pairCode ![modelNumeral M 16,modelWord [false,false] x]] := by
  let y := modelWord [false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 31,F pairCode ![modelNumeral M 8,y+y]]) =
    F pairCode ![modelNumeral M 38,F pairCode ![modelNumeral M 16,y]]
  have h := rightZero 31 0 38 (by decide) (by decide +kernel) (modelNumeral M 8) y
  have hn : modelNumeral M 8+modelNumeral M 8+modelNumeral M 0 = modelNumeral M 16 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row4 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 38,F pairCode ![modelNumeral M 16,modelWord [false,false] x]]) =
    F pairCode ![modelNumeral M 52,F pairCode ![modelNumeral M 32,modelWord [false] x]] := by
  let y := modelWord [false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 38,F pairCode ![modelNumeral M 16,y+y]]) =
    F pairCode ![modelNumeral M 52,F pairCode ![modelNumeral M 32,y]]
  have h := rightZero 38 0 52 (by decide) (by decide +kernel) (modelNumeral M 16) y
  have hn : modelNumeral M 16+modelNumeral M 16+modelNumeral M 0 = modelNumeral M 32 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row5 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 52,F pairCode ![modelNumeral M 32,modelWord [false] x]]) =
    F pairCode ![modelNumeral M 73,F pairCode ![modelNumeral M 64,modelWord [] x]] := by
  let y := modelWord [] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 52,F pairCode ![modelNumeral M 32,y+y]]) =
    F pairCode ![modelNumeral M 73,F pairCode ![modelNumeral M 64,y]]
  have h := rightZero 52 0 73 (by decide) (by decide +kernel) (modelNumeral M 32) y
  have hn : modelNumeral M 32+modelNumeral M 32+modelNumeral M 0 = modelNumeral M 64 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem prefixWord (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 6,F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [false,false,false,false,false,false] x]]] =
    F pairCode ![modelNumeral M 73,F pairCode ![modelNumeral M 64,modelWord [] x]] := by
  rw [PA194Site30Jump.standardRunCorrect]
  simp only [PA194Site30Jump.standardRun]
  rw [row0,row1,row2,row3,row4,row5]
#print axioms prefixWord
end models
end PA194Site0Prefix
