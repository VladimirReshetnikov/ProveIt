import PA194Site30Jump
import PA194Site32PositivePath
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace PA194Site3668Prefix
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
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,true,true,true,true,false] x]]) =
    F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,modelWord [false,true,true,true,true,false] x]] := by
  let y := modelWord [false,true,true,true,true,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,y+y+1]]) =
    F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,y]]
  have h := rightOne 24 1 26 (by decide) (by decide +kernel) (modelNumeral M 1) y
  have hn : modelNumeral M 1+modelNumeral M 1+modelNumeral M 1 = modelNumeral M 3 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row1 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,modelWord [false,true,true,true,true,false] x]]) =
    F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,modelWord [true,true,true,true,false] x]] := by
  let y := modelWord [true,true,true,true,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,y+y]]) =
    F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,y]]
  have h := rightZero 26 0 29 (by decide) (by decide +kernel) (modelNumeral M 3) y
  have hn : modelNumeral M 3+modelNumeral M 3+modelNumeral M 0 = modelNumeral M 6 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row2 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,modelWord [true,true,true,true,false] x]]) =
    F pairCode ![modelNumeral M 35,F pairCode ![modelNumeral M 13,modelWord [true,true,true,false] x]] := by
  let y := modelWord [true,true,true,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,y+y+1]]) =
    F pairCode ![modelNumeral M 35,F pairCode ![modelNumeral M 13,y]]
  have h := rightOne 29 1 35 (by decide) (by decide +kernel) (modelNumeral M 6) y
  have hn : modelNumeral M 6+modelNumeral M 6+modelNumeral M 1 = modelNumeral M 13 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row3 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 35,F pairCode ![modelNumeral M 13,modelWord [true,true,true,false] x]]) =
    F pairCode ![modelNumeral M 47,F pairCode ![modelNumeral M 27,modelWord [true,true,false] x]] := by
  let y := modelWord [true,true,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 35,F pairCode ![modelNumeral M 13,y+y+1]]) =
    F pairCode ![modelNumeral M 47,F pairCode ![modelNumeral M 27,y]]
  have h := rightOne 35 1 47 (by decide) (by decide +kernel) (modelNumeral M 13) y
  have hn : modelNumeral M 13+modelNumeral M 13+modelNumeral M 1 = modelNumeral M 27 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row4 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 47,F pairCode ![modelNumeral M 27,modelWord [true,true,false] x]]) =
    F pairCode ![modelNumeral M 67,F pairCode ![modelNumeral M 55,modelWord [true,false] x]] := by
  let y := modelWord [true,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 47,F pairCode ![modelNumeral M 27,y+y+1]]) =
    F pairCode ![modelNumeral M 67,F pairCode ![modelNumeral M 55,y]]
  have h := rightOne 47 1 67 (by decide) (by decide +kernel) (modelNumeral M 27) y
  have hn : modelNumeral M 27+modelNumeral M 27+modelNumeral M 1 = modelNumeral M 55 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row5 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 67,F pairCode ![modelNumeral M 55,modelWord [true,false] x]]) =
    F pairCode ![modelNumeral M 33,F pairCode ![modelNumeral M 111,modelWord [false] x]] := by
  let y := modelWord [false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 67,F pairCode ![modelNumeral M 55,y+y+1]]) =
    F pairCode ![modelNumeral M 33,F pairCode ![modelNumeral M 111,y]]
  have h := rightOne 67 1 33 (by decide) (by decide +kernel) (modelNumeral M 55) y
  have hn : modelNumeral M 55+modelNumeral M 55+modelNumeral M 1 = modelNumeral M 111 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row6 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 33,F pairCode ![modelNumeral M 111,modelWord [false] x]]) =
    F pairCode ![modelNumeral M 42,F pairCode ![modelNumeral M 222,modelWord [] x]] := by
  let y := modelWord [] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 33,F pairCode ![modelNumeral M 111,y+y]]) =
    F pairCode ![modelNumeral M 42,F pairCode ![modelNumeral M 222,y]]
  have h := rightZero 33 0 42 (by decide) (by decide +kernel) (modelNumeral M 111) y
  have hn : modelNumeral M 111+modelNumeral M 111+modelNumeral M 0 = modelNumeral M 222 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem prefixWord (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 7,F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,true,true,true,true,false] x]]] =
    F pairCode ![modelNumeral M 42,F pairCode ![modelNumeral M 222,modelWord [] x]] := by
  rw [PA194Site30Jump.standardRunCorrect]
  simp only [PA194Site30Jump.standardRun]
  rw [row0,row1,row2,row3,row4,row5,row6]
#print axioms prefixWord
end models
end PA194Site3668Prefix
