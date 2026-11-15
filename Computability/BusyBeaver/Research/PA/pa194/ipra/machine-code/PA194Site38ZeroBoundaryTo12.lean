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
namespace PA194Site38ZeroBoundaryTo12
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
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 11,F pairCode ![modelNumeral M 6452,modelWord [false] x]]) =
    F pairCode ![modelNumeral M 8,F pairCode ![modelNumeral M 3226,modelWord [false,true] x]] := by
  let y := modelWord [] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 11,F pairCode ![modelNumeral M 6452,y+y]]) =
    F pairCode ![modelNumeral M 8,F pairCode ![modelNumeral M 3226,(y+y+1)+(y+y+1)]]
  have h := leftZeroWriteOne 11 8 (by decide) (by decide +kernel) (modelNumeral M 6452) y
  have hn : modelNumeral M 6452 = modelNumeral M 3226+modelNumeral M 3226 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 6452) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 3226)).1]
  have hh : F halfCode (fun _ => modelNumeral M 6452) = modelNumeral M 3226 := by rw [hn,(modelDouble (modelNumeral M 3226)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row1 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 8,F pairCode ![modelNumeral M 3226,modelWord [false,true] x]]) =
    F pairCode ![modelNumeral M 10,F pairCode ![modelNumeral M 1613,modelWord [false,false,true] x]] := by
  let y := modelWord [true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 8,F pairCode ![modelNumeral M 3226,y+y]]) =
    F pairCode ![modelNumeral M 10,F pairCode ![modelNumeral M 1613,(y+y)+(y+y)]]
  have h := leftZero 8 10 (by decide) (by decide +kernel) (modelNumeral M 3226) y
  have hn : modelNumeral M 3226 = modelNumeral M 1613+modelNumeral M 1613 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 3226) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 1613)).1]
  have hh : F halfCode (fun _ => modelNumeral M 3226) = modelNumeral M 1613 := by rw [hn,(modelDouble (modelNumeral M 1613)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row2 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 10,F pairCode ![modelNumeral M 1613,modelWord [false,false,true] x]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 806,modelWord [true,false,false,true] x]] := by
  let y := modelWord [false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 10,F pairCode ![modelNumeral M 1613,y+y]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 806,(y+y)+(y+y)+1]]
  have h := leftZero 10 9 (by decide) (by decide +kernel) (modelNumeral M 1613) y
  have hn : modelNumeral M 1613 = modelNumeral M 806+modelNumeral M 806+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 1613) = (1 : M) := by rw [hn,(modelOdd (modelNumeral M 806)).1]
  have hh : F halfCode (fun _ => modelNumeral M 1613) = modelNumeral M 806 := by rw [hn,(modelOdd (modelNumeral M 806)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row3 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 806,modelWord [true,false,false,true] x]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 403,modelWord [false,false,false,false,true] x]] := by
  let y := modelWord [false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 806,y+y+1]]) =
    F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 403,(y+y)+(y+y)]]
  have h := leftOne 9 9 (by decide) (by decide +kernel) (modelNumeral M 806) y
  have hn : modelNumeral M 806 = modelNumeral M 403+modelNumeral M 403 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 806) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 403)).1]
  have hh : F halfCode (fun _ => modelNumeral M 806) = modelNumeral M 403 := by rw [hn,(modelDouble (modelNumeral M 403)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row4 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 403,modelWord [false,false,false,false,true] x]]) =
    F pairCode ![modelNumeral M 12,F pairCode ![modelNumeral M 807,modelWord [false,false,false,true] x]] := by
  let y := modelWord [false,false,false,true] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 9,F pairCode ![modelNumeral M 403,y+y]]) =
    F pairCode ![modelNumeral M 12,F pairCode ![modelNumeral M 807,y]]
  have h := rightZero 9 1 12 (by decide) (by decide +kernel) (modelNumeral M 403) y
  have hn : modelNumeral M 403+modelNumeral M 403+modelNumeral M 1 = modelNumeral M 807 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem fiveRows (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 5,F pairCode ![modelNumeral M 11,F pairCode ![modelNumeral M 6452,modelWord [false] x]]] =
    F pairCode ![modelNumeral M 12,F pairCode ![modelNumeral M 807,modelWord [false,false,false,true] x]] := by
  rw [PA194Site30Jump.standardRunCorrect]
  simp only [PA194Site30Jump.standardRun]
  rw [row0,row1,row2,row3,row4]
#print axioms fiveRows
end models
end PA194Site38ZeroBoundaryTo12
