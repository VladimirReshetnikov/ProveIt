import PA194Site30Jump
import PA194Site32PositivePath
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace PA194Site3671ThirdPrefix
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
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,true,false,false,true] x]]) =
    F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,modelWord [true,false,false,true] x]] := by
  let y := modelWord [true,false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,y+y+1]]) =
    F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,y]]
  have h := rightOne 24 1 26 (by decide) (by decide +kernel) (modelNumeral M 1) y
  have hn : modelNumeral M 1+modelNumeral M 1+modelNumeral M 1 = modelNumeral M 3 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row1 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,modelWord [true,false,false,true] x]]) =
    F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 7,modelWord [false,false,true] x]] := by
  let y := modelWord [false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,y+y+1]]) =
    F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 7,y]]
  have h := rightOne 26 1 30 (by decide) (by decide +kernel) (modelNumeral M 3) y
  have hn : modelNumeral M 3+modelNumeral M 3+modelNumeral M 1 = modelNumeral M 7 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row2 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 7,modelWord [false,false,true] x]]) =
    F pairCode ![modelNumeral M 36,F pairCode ![modelNumeral M 3,modelWord [true,false,false,true] x]] := by
  let y := modelWord [false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 7,y+y]]) =
    F pairCode ![modelNumeral M 36,F pairCode ![modelNumeral M 3,(y+y)+(y+y)+1]]
  have h := leftZero 30 36 (by decide) (by decide +kernel) (modelNumeral M 7) y
  have hn : modelNumeral M 7 = modelNumeral M 3+modelNumeral M 3+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 7) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M 3)).1]
  have hh : F halfCode (fun _ => modelNumeral M 7) = modelNumeral M 3 := by rw [hn,(modelOdd (modelNumeral M 3)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row3 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 36,F pairCode ![modelNumeral M 3,modelWord [true,false,false,true] x]]) =
    F pairCode ![modelNumeral M 49,F pairCode ![modelNumeral M 7,modelWord [false,false,true] x]] := by
  let y := modelWord [false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 36,F pairCode ![modelNumeral M 3,y+y+1]]) =
    F pairCode ![modelNumeral M 49,F pairCode ![modelNumeral M 7,y]]
  have h := rightOne 36 1 49 (by decide) (by decide +kernel) (modelNumeral M 3) y
  have hn : modelNumeral M 3+modelNumeral M 3+modelNumeral M 1 = modelNumeral M 7 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row4 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 49,F pairCode ![modelNumeral M 7,modelWord [false,false,true] x]]) =
    F pairCode ![modelNumeral M 69,F pairCode ![modelNumeral M 14,modelWord [false,true] x]] := by
  let y := modelWord [false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 49,F pairCode ![modelNumeral M 7,y+y]]) =
    F pairCode ![modelNumeral M 69,F pairCode ![modelNumeral M 14,y]]
  have h := rightZero 49 0 69 (by decide) (by decide +kernel) (modelNumeral M 7) y
  have hn : modelNumeral M 7+modelNumeral M 7+modelNumeral M 0 = modelNumeral M 14 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row5 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 69,F pairCode ![modelNumeral M 14,modelWord [false,true] x]]) =
    F pairCode ![modelNumeral M 94,F pairCode ![modelNumeral M 7,modelWord [false,false,true] x]] := by
  let y := modelWord [true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 69,F pairCode ![modelNumeral M 14,y+y]]) =
    F pairCode ![modelNumeral M 94,F pairCode ![modelNumeral M 7,(y+y)+(y+y)]]
  have h := leftZero 69 94 (by decide) (by decide +kernel) (modelNumeral M 14) y
  have hn : modelNumeral M 14 = modelNumeral M 7+modelNumeral M 7 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 14) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 7)).1]
  have hh : F halfCode (fun _ => modelNumeral M 14) = modelNumeral M 7 := by rw [hn,(modelDouble (modelNumeral M 7)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row6 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 94,F pairCode ![modelNumeral M 7,modelWord [false,false,true] x]]) =
    F pairCode ![modelNumeral M 50,F pairCode ![modelNumeral M 14,modelWord [false,true] x]] := by
  let y := modelWord [false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 94,F pairCode ![modelNumeral M 7,y+y]]) =
    F pairCode ![modelNumeral M 50,F pairCode ![modelNumeral M 14,y]]
  have h := rightZero 94 0 50 (by decide) (by decide +kernel) (modelNumeral M 7) y
  have hn : modelNumeral M 7+modelNumeral M 7+modelNumeral M 0 = modelNumeral M 14 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row7 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 50,F pairCode ![modelNumeral M 14,modelWord [false,true] x]]) =
    F pairCode ![modelNumeral M 70,F pairCode ![modelNumeral M 28,modelWord [true] x]] := by
  let y := modelWord [true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 50,F pairCode ![modelNumeral M 14,y+y]]) =
    F pairCode ![modelNumeral M 70,F pairCode ![modelNumeral M 28,y]]
  have h := rightZero 50 0 70 (by decide) (by decide +kernel) (modelNumeral M 14) y
  have hn : modelNumeral M 14+modelNumeral M 14+modelNumeral M 0 = modelNumeral M 28 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row8 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 70,F pairCode ![modelNumeral M 28,modelWord [true] x]]) =
    F pairCode ![modelNumeral M 2,F pairCode ![modelNumeral M 56,modelWord [] x]] := by
  let y := modelWord [] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 70,F pairCode ![modelNumeral M 28,y+y+1]]) =
    F pairCode ![modelNumeral M 2,F pairCode ![modelNumeral M 56,y]]
  have h := rightOne 70 0 2 (by decide) (by decide +kernel) (modelNumeral M 28) y
  have hn : modelNumeral M 28+modelNumeral M 28+modelNumeral M 0 = modelNumeral M 56 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem prefixWord (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 9,F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,true,false,false,true] x]]] =
    F pairCode ![modelNumeral M 2,F pairCode ![modelNumeral M 56,modelWord [] x]] := by
  rw [PA194Site30Jump.standardRunCorrect]
  simp only [PA194Site30Jump.standardRun]
  rw [row0,row1,row2,row3,row4,row5,row6,row7,row8]
#print axioms prefixWord
end models
end PA194Site3671ThirdPrefix
