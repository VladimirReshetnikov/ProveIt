import PA194Site30Jump
import PA194Site32PositivePath
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace PA194Site48RootReturn
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
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 13,modelWord [false,false] x]]) =
    F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 6,modelWord [true,false,false] x]] := by
  let y := modelWord [false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 13,y+y]]) =
    F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 6,(y+y)+(y+y)+1]]
  have h := leftZero 17 18 (by decide) (by decide +kernel) (modelNumeral M 13) y
  have hn : modelNumeral M 13 = modelNumeral M 6+modelNumeral M 6+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 13) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M 6)).1]
  have hh : F halfCode (fun _ => modelNumeral M 13) = modelNumeral M 6 := by rw [hn,(modelOdd (modelNumeral M 6)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row1 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 6,modelWord [true,false,false] x]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 3,modelWord [false,true,false,false] x]] := by
  let y := modelWord [false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 6,y+y+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 3,(y+y+1)+(y+y+1)]]
  have h := leftOneWriteOne 18 16 (by decide) (by decide +kernel) (modelNumeral M 6) y
  have hn : modelNumeral M 6 = modelNumeral M 3+modelNumeral M 3 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 6) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 3)).1]
  have hh : F halfCode (fun _ => modelNumeral M 6) = modelNumeral M 3 := by rw [hn,(modelDouble (modelNumeral M 3)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row2 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 3,modelWord [false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 1,modelWord [true,false,true,false,false] x]] := by
  let y := modelWord [true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 3,y+y]]) =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 1,(y+y)+(y+y)+1]]
  have h := leftZero 16 17 (by decide) (by decide +kernel) (modelNumeral M 3) y
  have hn : modelNumeral M 3 = modelNumeral M 1+modelNumeral M 1+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 3) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M 1)).1]
  have hh : F halfCode (fun _ => modelNumeral M 3) = modelNumeral M 1 := by rw [hn,(modelOdd (modelNumeral M 1)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row3 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 1,modelWord [true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,modelWord [true,true,false,true,false,false] x]] := by
  let y := modelWord [false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 1,y+y+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,(y+y+1)+(y+y+1)+1]]
  have h := leftOneWriteOne 17 16 (by decide) (by decide +kernel) (modelNumeral M 1) y
  have hn : modelNumeral M 1 = modelNumeral M 0+modelNumeral M 0+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 1) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 1) = modelNumeral M 0 := by rw [hn,(modelOdd (modelNumeral M 0)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row4 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,modelWord [true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,modelWord [false,true,true,false,true,false,false] x]] := by
  let y := modelWord [true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,y+y+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,(y+y+1)+(y+y+1)]]
  have h := leftOneWriteOne 16 16 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by rw [hn,(modelDouble (modelNumeral M 0)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row5 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,modelWord [false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 0,modelWord [false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 16 17 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by rw [hn,(modelDouble (modelNumeral M 0)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row6 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 0,modelWord [false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 0,modelWord [false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 17 18 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by rw [hn,(modelDouble (modelNumeral M 0)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row7 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 0,modelWord [false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 18 19 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by rw [hn,(modelDouble (modelNumeral M 0)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row8 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 20,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 20,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 19 20 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by rw [hn,(modelDouble (modelNumeral M 0)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row9 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 20,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 21,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 20,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 21,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 20 21 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by rw [hn,(modelDouble (modelNumeral M 0)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row10 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 21,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 22,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,false,false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 21,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 22,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 21 22 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by rw [hn,(modelDouble (modelNumeral M 0)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row11 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 22,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,false,false,false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 22,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 22 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by rw [hn,(modelDouble (modelNumeral M 0)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row12 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,false,false,false,false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row13 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,false,false,false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row14 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,false,false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row15 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row16 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row17 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row18 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,true,true,false,true,false,false] x]] := by
  let y := modelWord [false,true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row19 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [true,true,false,true,false,false] x]] := by
  let y := modelWord [true,true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row20 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [true,true,false,true,false,false] x]]) =
    F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,true,false,false] x]] := by
  let y := modelWord [true,false,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y+1]]) =
    F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,y]]
  have h := rightOne 23 1 24 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 1 = modelNumeral M 1 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem returnWord (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 21,F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 13,modelWord [false,false] x]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,true,false,false] x]] := by
  rw [PA194Site30Jump.standardRunCorrect]
  simp only [PA194Site30Jump.standardRun]
  rw [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20]
#print axioms returnWord
end models
end PA194Site48RootReturn
