import PA194Site30Jump
import PA194Site32PositivePath
import PA194LeftRows
import PA194LeftZeroWriteOne
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace PA194Site3668ZeroBoundaryTo12
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194LeftRows PA194LeftZeroWriteOne PA194LeftOneRows PA194LeftOneWriteOne PA194RightRows PRAModelIOpenPairing
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
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 11,F pairCode ![modelNumeral M 444,modelWord [false] x]]) =
    F pairCode ![modelNumeral M 8,F pairCode ![modelNumeral M 222,modelWord [false,true] x]] := by
  let y := modelWord [] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 11,F pairCode ![modelNumeral M 444,y+y]]) =
    F pairCode ![modelNumeral M 8,F pairCode ![modelNumeral M 222,(y+y+1)+(y+y+1)]]
  have h := leftZeroWriteOne 11 8 (by decide) (by decide +kernel) (modelNumeral M 444) y
  have hn : modelNumeral M 444 = modelNumeral M 222+modelNumeral M 222 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 444) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 222)).1]
  have hh : F halfCode (fun _ => modelNumeral M 444) = modelNumeral M 222 := by rw [hn,(modelDouble (modelNumeral M 222)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row1 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 8,F pairCode ![modelNumeral M 222,modelWord [false,true] x]]) =
    F pairCode ![modelNumeral M 10,F pairCode ![modelNumeral M 111,modelWord [false,false,true] x]] := by
  let y := modelWord [true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 8,F pairCode ![modelNumeral M 222,y+y]]) =
    F pairCode ![modelNumeral M 10,F pairCode ![modelNumeral M 111,(y+y)+(y+y)]]
  have h := leftZero 8 10 (by decide) (by decide +kernel) (modelNumeral M 222) y
  have hn : modelNumeral M 222 = modelNumeral M 111+modelNumeral M 111 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 222) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 111)).1]
  have hh : F halfCode (fun _ => modelNumeral M 222) = modelNumeral M 111 := by rw [hn,(modelDouble (modelNumeral M 111)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row2 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 10,F pairCode ![modelNumeral M 111,modelWord [false,false,true] x]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 55,modelWord [true,false,false,true] x]] := by
  let y := modelWord [false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 10,F pairCode ![modelNumeral M 111,y+y]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 55,(y+y)+(y+y)+1]]
  have h := leftZero 10 9 (by decide) (by decide +kernel) (modelNumeral M 111) y
  have hn : modelNumeral M 111 = modelNumeral M 55+modelNumeral M 55+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 111) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M 55)).1]
  have hh : F halfCode (fun _ => modelNumeral M 111) = modelNumeral M 55 := by rw [hn,(modelOdd (modelNumeral M 55)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row3 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 55,modelWord [true,false,false,true] x]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 27,modelWord [true,false,false,false,true] x]] := by
  let y := modelWord [false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 55,y+y+1]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 27,(y+y)+(y+y)+1]]
  have h := leftOne 9 9 (by decide) (by decide +kernel) (modelNumeral M 55) y
  have hn : modelNumeral M 55 = modelNumeral M 27+modelNumeral M 27+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 55) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M 27)).1]
  have hh : F halfCode (fun _ => modelNumeral M 55) = modelNumeral M 27 := by rw [hn,(modelOdd (modelNumeral M 27)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row4 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 27,modelWord [true,false,false,false,true] x]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 13,modelWord [true,false,false,false,false,true] x]] := by
  let y := modelWord [false,false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 27,y+y+1]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 13,(y+y)+(y+y)+1]]
  have h := leftOne 9 9 (by decide) (by decide +kernel) (modelNumeral M 27) y
  have hn : modelNumeral M 27 = modelNumeral M 13+modelNumeral M 13+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 27) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M 13)).1]
  have hh : F halfCode (fun _ => modelNumeral M 27) = modelNumeral M 13 := by rw [hn,(modelOdd (modelNumeral M 13)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row5 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 13,modelWord [true,false,false,false,false,true] x]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 6,modelWord [true,false,false,false,false,false,true] x]] := by
  let y := modelWord [false,false,false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 13,y+y+1]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 6,(y+y)+(y+y)+1]]
  have h := leftOne 9 9 (by decide) (by decide +kernel) (modelNumeral M 13) y
  have hn : modelNumeral M 13 = modelNumeral M 6+modelNumeral M 6+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 13) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M 6)).1]
  have hh : F halfCode (fun _ => modelNumeral M 13) = modelNumeral M 6 := by rw [hn,(modelOdd (modelNumeral M 6)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row6 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 6,modelWord [true,false,false,false,false,false,true] x]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 3,modelWord [false,false,false,false,false,false,false,true] x]] := by
  let y := modelWord [false,false,false,false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 6,y+y+1]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 3,(y+y)+(y+y)]]
  have h := leftOne 9 9 (by decide) (by decide +kernel) (modelNumeral M 6) y
  have hn : modelNumeral M 6 = modelNumeral M 3+modelNumeral M 3 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 6) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 3)).1]
  have hh : F halfCode (fun _ => modelNumeral M 6) = modelNumeral M 3 := by rw [hn,(modelDouble (modelNumeral M 3)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row7 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 3,modelWord [false,false,false,false,false,false,false,true] x]]) =
    F pairCode ![modelNumeral M 12,F pairCode ![modelNumeral M 7,modelWord [false,false,false,false,false,false,true] x]] := by
  let y := modelWord [false,false,false,false,false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 3,y+y]]) =
    F pairCode ![modelNumeral M 12,F pairCode ![modelNumeral M 7,y]]
  have h := rightZero 9 1 12 (by decide) (by decide +kernel) (modelNumeral M 3) y
  have hn : modelNumeral M 3+modelNumeral M 3+modelNumeral M 1 = modelNumeral M 7 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem eightRows (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 8,F pairCode ![modelNumeral M 11,F pairCode ![modelNumeral M 444,modelWord [false] x]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![modelNumeral M 7,modelWord [false,false,false,false,false,false,true] x]] := by
  rw [PA194Site30Jump.standardRunCorrect]
  simp only [PA194Site30Jump.standardRun]
  rw [row0,row1,row2,row3,row4,row5,row6,row7]
#print axioms eightRows
end models
end PA194Site3668ZeroBoundaryTo12
