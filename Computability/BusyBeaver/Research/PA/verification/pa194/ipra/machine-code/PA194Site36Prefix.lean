import PA194Site30Jump
import PA194Site32PositivePath
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace PA194Site36Prefix
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
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,false,true,false,false,true,true,false,false,false] x]]) =
    F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,modelWord [false,false,true,false,false,true,true,false,false,false] x]] := by
  let y := modelWord [false,false,true,false,false,true,true,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,y+y+1]]) =
    F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,y]]
  have h := rightOne 24 1 26 (by decide) (by decide +kernel) (modelNumeral M 1) y
  have hn : modelNumeral M 1+modelNumeral M 1+modelNumeral M 1 = modelNumeral M 3 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row1 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,modelWord [false,false,true,false,false,true,true,false,false,false] x]]) =
    F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,modelWord [false,true,false,false,true,true,false,false,false] x]] := by
  let y := modelWord [false,true,false,false,true,true,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,y+y]]) =
    F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,y]]
  have h := rightZero 26 0 29 (by decide) (by decide +kernel) (modelNumeral M 3) y
  have hn : modelNumeral M 3+modelNumeral M 3+modelNumeral M 0 = modelNumeral M 6 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row2 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,modelWord [false,true,false,false,true,true,false,false,false] x]]) =
    F pairCode ![modelNumeral M 34,F pairCode ![modelNumeral M 12,modelWord [true,false,false,true,true,false,false,false] x]] := by
  let y := modelWord [true,false,false,true,true,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,y+y]]) =
    F pairCode ![modelNumeral M 34,F pairCode ![modelNumeral M 12,y]]
  have h := rightZero 29 0 34 (by decide) (by decide +kernel) (modelNumeral M 6) y
  have hn : modelNumeral M 6+modelNumeral M 6+modelNumeral M 0 = modelNumeral M 12 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row3 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 34,F pairCode ![modelNumeral M 12,modelWord [true,false,false,true,true,false,false,false] x]]) =
    F pairCode ![modelNumeral M 45,F pairCode ![modelNumeral M 25,modelWord [false,false,true,true,false,false,false] x]] := by
  let y := modelWord [false,false,true,true,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 34,F pairCode ![modelNumeral M 12,y+y+1]]) =
    F pairCode ![modelNumeral M 45,F pairCode ![modelNumeral M 25,y]]
  have h := rightOne 34 1 45 (by decide) (by decide +kernel) (modelNumeral M 12) y
  have hn : modelNumeral M 12+modelNumeral M 12+modelNumeral M 1 = modelNumeral M 25 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row4 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 45,F pairCode ![modelNumeral M 25,modelWord [false,false,true,true,false,false,false] x]]) =
    F pairCode ![modelNumeral M 55,F pairCode ![modelNumeral M 50,modelWord [false,true,true,false,false,false] x]] := by
  let y := modelWord [false,true,true,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 45,F pairCode ![modelNumeral M 25,y+y]]) =
    F pairCode ![modelNumeral M 55,F pairCode ![modelNumeral M 50,y]]
  have h := rightZero 45 0 55 (by decide) (by decide +kernel) (modelNumeral M 25) y
  have hn : modelNumeral M 25+modelNumeral M 25+modelNumeral M 0 = modelNumeral M 50 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row5 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 55,F pairCode ![modelNumeral M 50,modelWord [false,true,true,false,false,false] x]]) =
    F pairCode ![modelNumeral M 76,F pairCode ![modelNumeral M 100,modelWord [true,true,false,false,false] x]] := by
  let y := modelWord [true,true,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 55,F pairCode ![modelNumeral M 50,y+y]]) =
    F pairCode ![modelNumeral M 76,F pairCode ![modelNumeral M 100,y]]
  have h := rightZero 55 0 76 (by decide) (by decide +kernel) (modelNumeral M 50) y
  have hn : modelNumeral M 50+modelNumeral M 50+modelNumeral M 0 = modelNumeral M 100 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row6 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 76,F pairCode ![modelNumeral M 100,modelWord [true,true,false,false,false] x]]) =
    F pairCode ![modelNumeral M 37,F pairCode ![modelNumeral M 201,modelWord [true,false,false,false] x]] := by
  let y := modelWord [true,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 76,F pairCode ![modelNumeral M 100,y+y+1]]) =
    F pairCode ![modelNumeral M 37,F pairCode ![modelNumeral M 201,y]]
  have h := rightOne 76 1 37 (by decide) (by decide +kernel) (modelNumeral M 100) y
  have hn : modelNumeral M 100+modelNumeral M 100+modelNumeral M 1 = modelNumeral M 201 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row7 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 37,F pairCode ![modelNumeral M 201,modelWord [true,false,false,false] x]]) =
    F pairCode ![modelNumeral M 51,F pairCode ![modelNumeral M 403,modelWord [false,false,false] x]] := by
  let y := modelWord [false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 37,F pairCode ![modelNumeral M 201,y+y+1]]) =
    F pairCode ![modelNumeral M 51,F pairCode ![modelNumeral M 403,y]]
  have h := rightOne 37 1 51 (by decide) (by decide +kernel) (modelNumeral M 201) y
  have hn : modelNumeral M 201+modelNumeral M 201+modelNumeral M 1 = modelNumeral M 403 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row8 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 51,F pairCode ![modelNumeral M 403,modelWord [false,false,false] x]]) =
    F pairCode ![modelNumeral M 72,F pairCode ![modelNumeral M 806,modelWord [false,false] x]] := by
  let y := modelWord [false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 51,F pairCode ![modelNumeral M 403,y+y]]) =
    F pairCode ![modelNumeral M 72,F pairCode ![modelNumeral M 806,y]]
  have h := rightZero 51 0 72 (by decide) (by decide +kernel) (modelNumeral M 403) y
  have hn : modelNumeral M 403+modelNumeral M 403+modelNumeral M 0 = modelNumeral M 806 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row9 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 72,F pairCode ![modelNumeral M 806,modelWord [false,false] x]]) =
    F pairCode ![modelNumeral M 75,F pairCode ![modelNumeral M 1612,modelWord [false] x]] := by
  let y := modelWord [false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 72,F pairCode ![modelNumeral M 806,y+y]]) =
    F pairCode ![modelNumeral M 75,F pairCode ![modelNumeral M 1612,y]]
  have h := rightZero 72 0 75 (by decide) (by decide +kernel) (modelNumeral M 806) y
  have hn : modelNumeral M 806+modelNumeral M 806+modelNumeral M 0 = modelNumeral M 1612 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row10 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 75,F pairCode ![modelNumeral M 1612,modelWord [false] x]]) =
    F pairCode ![modelNumeral M 42,F pairCode ![modelNumeral M 3224,modelWord [] x]] := by
  let y := modelWord [] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 75,F pairCode ![modelNumeral M 1612,y+y]]) =
    F pairCode ![modelNumeral M 42,F pairCode ![modelNumeral M 3224,y]]
  have h := rightZero 75 0 42 (by decide) (by decide +kernel) (modelNumeral M 1612) y
  have hn : modelNumeral M 1612+modelNumeral M 1612+modelNumeral M 0 = modelNumeral M 3224 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem prefixWord (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 11,F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,false,true,false,false,true,true,false,false,false] x]]] =
    F pairCode ![modelNumeral M 42,F pairCode ![modelNumeral M 3224,modelWord [] x]] := by
  rw [PA194Site30Jump.standardRunCorrect]
  simp only [PA194Site30Jump.standardRun]
  rw [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10]
#print axioms prefixWord
end models
end PA194Site36Prefix
