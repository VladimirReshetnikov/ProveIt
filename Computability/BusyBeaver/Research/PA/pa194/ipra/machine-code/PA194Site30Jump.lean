import PA194Path30Header
import PA194Path29Input
import PA194LeftRows
import PA194LeftOneRows
import PA194LeftOneWriteOne
import PA194RightRows
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 12000000
namespace PA194Site30Jump
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
theorem row0 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,false,false,true,false,true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,modelWord [false,false,false,true,false,true,true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,true,false,true,true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,y+y+1]]) =
    F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,y]]
  have h := rightOne 24 1 26 (by decide) (by decide +kernel) (modelNumeral M 1) y
  have hn : modelNumeral M 1+modelNumeral M 1+modelNumeral M 1 = modelNumeral M 3 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row1 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,modelWord [false,false,false,true,false,true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,modelWord [false,false,true,false,true,true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,true,false,true,true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 26,F pairCode ![modelNumeral M 3,y+y]]) =
    F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,y]]
  have h := rightZero 26 0 29 (by decide) (by decide +kernel) (modelNumeral M 3) y
  have hn : modelNumeral M 3+modelNumeral M 3+modelNumeral M 0 = modelNumeral M 6 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row2 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,modelWord [false,false,true,false,true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 34,F pairCode ![modelNumeral M 12,modelWord [false,true,false,true,true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,true,false,true,true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 29,F pairCode ![modelNumeral M 6,y+y]]) =
    F pairCode ![modelNumeral M 34,F pairCode ![modelNumeral M 12,y]]
  have h := rightZero 29 0 34 (by decide) (by decide +kernel) (modelNumeral M 6) y
  have hn : modelNumeral M 6+modelNumeral M 6+modelNumeral M 0 = modelNumeral M 12 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row3 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 34,F pairCode ![modelNumeral M 12,modelWord [false,true,false,true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 44,F pairCode ![modelNumeral M 24,modelWord [true,false,true,true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,false,true,true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 34,F pairCode ![modelNumeral M 12,y+y]]) =
    F pairCode ![modelNumeral M 44,F pairCode ![modelNumeral M 24,y]]
  have h := rightZero 34 0 44 (by decide) (by decide +kernel) (modelNumeral M 12) y
  have hn : modelNumeral M 12+modelNumeral M 12+modelNumeral M 0 = modelNumeral M 24 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row4 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 44,F pairCode ![modelNumeral M 24,modelWord [true,false,true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 63,F pairCode ![modelNumeral M 49,modelWord [false,true,true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,true,true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 44,F pairCode ![modelNumeral M 24,y+y+1]]) =
    F pairCode ![modelNumeral M 63,F pairCode ![modelNumeral M 49,y]]
  have h := rightOne 44 1 63 (by decide) (by decide +kernel) (modelNumeral M 24) y
  have hn : modelNumeral M 24+modelNumeral M 24+modelNumeral M 1 = modelNumeral M 49 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row5 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 63,F pairCode ![modelNumeral M 49,modelWord [false,true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 88,F pairCode ![modelNumeral M 98,modelWord [true,true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 63,F pairCode ![modelNumeral M 49,y+y]]) =
    F pairCode ![modelNumeral M 88,F pairCode ![modelNumeral M 98,y]]
  have h := rightZero 63 0 88 (by decide) (by decide +kernel) (modelNumeral M 49) y
  have hn : modelNumeral M 49+modelNumeral M 49+modelNumeral M 0 = modelNumeral M 98 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row6 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 88,F pairCode ![modelNumeral M 98,modelWord [true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 98,F pairCode ![modelNumeral M 197,modelWord [true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 88,F pairCode ![modelNumeral M 98,y+y+1]]) =
    F pairCode ![modelNumeral M 98,F pairCode ![modelNumeral M 197,y]]
  have h := rightOne 88 1 98 (by decide) (by decide +kernel) (modelNumeral M 98) y
  have hn : modelNumeral M 98+modelNumeral M 98+modelNumeral M 1 = modelNumeral M 197 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row7 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 98,F pairCode ![modelNumeral M 197,modelWord [true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 115,F pairCode ![modelNumeral M 98,modelWord [true,true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 98,F pairCode ![modelNumeral M 197,y+y+1]]) =
    F pairCode ![modelNumeral M 115,F pairCode ![modelNumeral M 98,(y+y+1)+(y+y+1)+1]]
  have h := leftOneWriteOne 98 115 (by decide) (by decide +kernel) (modelNumeral M 197) y
  have hn : modelNumeral M 197 = modelNumeral M 98+modelNumeral M 98+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 197) = (1 : M) := by
    rw [hn,(modelOdd (modelNumeral M 98)).1]
  have hh : F halfCode (fun _ => modelNumeral M 197) = modelNumeral M 98 := by
    rw [hn,(modelOdd (modelNumeral M 98)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row8 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 115,F pairCode ![modelNumeral M 98,modelWord [true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 67,F pairCode ![modelNumeral M 49,modelWord [false,true,true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 115,F pairCode ![modelNumeral M 98,y+y+1]]) =
    F pairCode ![modelNumeral M 67,F pairCode ![modelNumeral M 49,(y+y+1)+(y+y+1)]]
  have h := leftOneWriteOne 115 67 (by decide) (by decide +kernel) (modelNumeral M 98) y
  have hn : modelNumeral M 98 = modelNumeral M 49+modelNumeral M 49 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 98) = (0 : M) := by
    rw [hn,(modelDouble (modelNumeral M 49)).1]
  have hh : F halfCode (fun _ => modelNumeral M 98) = modelNumeral M 49 := by
    rw [hn,(modelDouble (modelNumeral M 49)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row9 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 67,F pairCode ![modelNumeral M 49,modelWord [false,true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 86,F pairCode ![modelNumeral M 98,modelWord [true,true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 67,F pairCode ![modelNumeral M 49,y+y]]) =
    F pairCode ![modelNumeral M 86,F pairCode ![modelNumeral M 98,y]]
  have h := rightZero 67 0 86 (by decide) (by decide +kernel) (modelNumeral M 49) y
  have hn : modelNumeral M 49+modelNumeral M 49+modelNumeral M 0 = modelNumeral M 98 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row10 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 86,F pairCode ![modelNumeral M 98,modelWord [true,true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 107,F pairCode ![modelNumeral M 197,modelWord [true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 86,F pairCode ![modelNumeral M 98,y+y+1]]) =
    F pairCode ![modelNumeral M 107,F pairCode ![modelNumeral M 197,y]]
  have h := rightOne 86 1 107 (by decide) (by decide +kernel) (modelNumeral M 98) y
  have hn : modelNumeral M 98+modelNumeral M 98+modelNumeral M 1 = modelNumeral M 197 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row11 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 107,F pairCode ![modelNumeral M 197,modelWord [true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 395,modelWord [true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 107,F pairCode ![modelNumeral M 197,y+y+1]]) =
    F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 395,y]]
  have h := rightOne 107 1 30 (by decide) (by decide +kernel) (modelNumeral M 197) y
  have hn : modelNumeral M 197+modelNumeral M 197+modelNumeral M 1 = modelNumeral M 395 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row12 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 395,modelWord [true,false,false] x]]) =
    F pairCode ![modelNumeral M 37,F pairCode ![modelNumeral M 197,modelWord [true,true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 30,F pairCode ![modelNumeral M 395,y+y+1]]) =
    F pairCode ![modelNumeral M 37,F pairCode ![modelNumeral M 197,(y+y+1)+(y+y+1)+1]]
  have h := leftOneWriteOne 30 37 (by decide) (by decide +kernel) (modelNumeral M 395) y
  have hn : modelNumeral M 395 = modelNumeral M 197+modelNumeral M 197+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 395) = (1 : M) := by
    rw [hn,(modelOdd (modelNumeral M 197)).1]
  have hh : F halfCode (fun _ => modelNumeral M 395) = modelNumeral M 197 := by
    rw [hn,(modelOdd (modelNumeral M 197)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row13 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 37,F pairCode ![modelNumeral M 197,modelWord [true,true,false,false] x]]) =
    F pairCode ![modelNumeral M 51,F pairCode ![modelNumeral M 395,modelWord [true,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 37,F pairCode ![modelNumeral M 197,y+y+1]]) =
    F pairCode ![modelNumeral M 51,F pairCode ![modelNumeral M 395,y]]
  have h := rightOne 37 1 51 (by decide) (by decide +kernel) (modelNumeral M 197) y
  have hn : modelNumeral M 197+modelNumeral M 197+modelNumeral M 1 = modelNumeral M 395 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row14 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 51,F pairCode ![modelNumeral M 395,modelWord [true,false,false] x]]) =
    F pairCode ![modelNumeral M 49,F pairCode ![modelNumeral M 197,modelWord [true,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 51,F pairCode ![modelNumeral M 395,y+y+1]]) =
    F pairCode ![modelNumeral M 49,F pairCode ![modelNumeral M 197,(y+y)+(y+y)+1]]
  have h := leftOne 51 49 (by decide) (by decide +kernel) (modelNumeral M 395) y
  have hn : modelNumeral M 395 = modelNumeral M 197+modelNumeral M 197+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 395) = (1 : M) := by
    rw [hn,(modelOdd (modelNumeral M 197)).1]
  have hh : F halfCode (fun _ => modelNumeral M 395) = modelNumeral M 197 := by
    rw [hn,(modelOdd (modelNumeral M 197)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row15 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 49,F pairCode ![modelNumeral M 197,modelWord [true,false,false,false] x]]) =
    F pairCode ![modelNumeral M 14,F pairCode ![modelNumeral M 98,modelWord [true,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 49,F pairCode ![modelNumeral M 197,y+y+1]]) =
    F pairCode ![modelNumeral M 14,F pairCode ![modelNumeral M 98,(y+y)+(y+y)+1]]
  have h := leftOne 49 14 (by decide) (by decide +kernel) (modelNumeral M 197) y
  have hn : modelNumeral M 197 = modelNumeral M 98+modelNumeral M 98+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 197) = (1 : M) := by
    rw [hn,(modelOdd (modelNumeral M 98)).1]
  have hh : F halfCode (fun _ => modelNumeral M 197) = modelNumeral M 98 := by
    rw [hn,(modelOdd (modelNumeral M 98)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row16 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 14,F pairCode ![modelNumeral M 98,modelWord [true,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 15,F pairCode ![modelNumeral M 49,modelWord [false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 14,F pairCode ![modelNumeral M 98,y+y+1]]) =
    F pairCode ![modelNumeral M 15,F pairCode ![modelNumeral M 49,(y+y)+(y+y)]]
  have h := leftOne 14 15 (by decide) (by decide +kernel) (modelNumeral M 98) y
  have hn : modelNumeral M 98 = modelNumeral M 49+modelNumeral M 49 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 98) = (0 : M) := by
    rw [hn,(modelDouble (modelNumeral M 49)).1]
  have hh : F halfCode (fun _ => modelNumeral M 98) = modelNumeral M 49 := by
    rw [hn,(modelDouble (modelNumeral M 49)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row17 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 15,F pairCode ![modelNumeral M 49,modelWord [false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 15,F pairCode ![modelNumeral M 24,modelWord [true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 15,F pairCode ![modelNumeral M 49,y+y]]) =
    F pairCode ![modelNumeral M 15,F pairCode ![modelNumeral M 24,(y+y)+(y+y)+1]]
  have h := leftZero 15 15 (by decide) (by decide +kernel) (modelNumeral M 49) y
  have hn : modelNumeral M 49 = modelNumeral M 24+modelNumeral M 24+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 49) = (1 : M) := by
    rw [hn,(modelOdd (modelNumeral M 24)).1]
  have hh : F halfCode (fun _ => modelNumeral M 49) = modelNumeral M 24 := by
    rw [hn,(modelOdd (modelNumeral M 24)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row18 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 15,F pairCode ![modelNumeral M 24,modelWord [true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 12,modelWord [false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 15,F pairCode ![modelNumeral M 24,y+y+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 12,(y+y+1)+(y+y+1)]]
  have h := leftOneWriteOne 15 16 (by decide) (by decide +kernel) (modelNumeral M 24) y
  have hn : modelNumeral M 24 = modelNumeral M 12+modelNumeral M 12 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 24) = (0 : M) := by
    rw [hn,(modelDouble (modelNumeral M 12)).1]
  have hh : F halfCode (fun _ => modelNumeral M 24) = modelNumeral M 12 := by
    rw [hn,(modelDouble (modelNumeral M 12)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row19 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 12,modelWord [false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 6,modelWord [false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 12,y+y]]) =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 6,(y+y)+(y+y)]]
  have h := leftZero 16 17 (by decide) (by decide +kernel) (modelNumeral M 12) y
  have hn : modelNumeral M 12 = modelNumeral M 6+modelNumeral M 6 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 12) = (0 : M) := by
    rw [hn,(modelDouble (modelNumeral M 6)).1]
  have hh : F halfCode (fun _ => modelNumeral M 12) = modelNumeral M 6 := by
    rw [hn,(modelDouble (modelNumeral M 6)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row20 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 6,modelWord [false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 3,modelWord [false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 6,y+y]]) =
    F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 3,(y+y)+(y+y)]]
  have h := leftZero 17 18 (by decide) (by decide +kernel) (modelNumeral M 6) y
  have hn : modelNumeral M 6 = modelNumeral M 3+modelNumeral M 3 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 6) = (0 : M) := by
    rw [hn,(modelDouble (modelNumeral M 3)).1]
  have hh : F halfCode (fun _ => modelNumeral M 6) = modelNumeral M 3 := by
    rw [hn,(modelDouble (modelNumeral M 3)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row21 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 3,modelWord [false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 1,modelWord [true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 3,y+y]]) =
    F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 1,(y+y)+(y+y)+1]]
  have h := leftZero 18 19 (by decide) (by decide +kernel) (modelNumeral M 3) y
  have hn : modelNumeral M 3 = modelNumeral M 1+modelNumeral M 1+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 3) = (1 : M) := by
    rw [hn,(modelOdd (modelNumeral M 1)).1]
  have hh : F halfCode (fun _ => modelNumeral M 3) = modelNumeral M 1 := by
    rw [hn,(modelOdd (modelNumeral M 1)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row22 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 1,modelWord [true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,modelWord [true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 1,y+y+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,(y+y+1)+(y+y+1)+1]]
  have h := leftOneWriteOne 19 16 (by decide) (by decide +kernel) (modelNumeral M 1) y
  have hn : modelNumeral M 1 = modelNumeral M 0+modelNumeral M 0+1 := by
    rw [←modelNumeralOne,←modelNumeralAdd,←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 1) = (1 : M) := by
    rw [hn,(modelOdd (modelNumeral M 0)).1]
  have hh : F halfCode (fun _ => modelNumeral M 1) = modelNumeral M 0 := by
    rw [hn,(modelOdd (modelNumeral M 0)).2]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row23 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,modelWord [true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,modelWord [false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,y+y+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,(y+y+1)+(y+y+1)]]
  have h := leftOneWriteOne 16 16 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by
    change F parityCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).1
    simpa only [zero_add] using h0
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by
    change F halfCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).2
    simpa only [zero_add] using h0
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row24 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,modelWord [false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 0,modelWord [false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 16 17 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by
    change F parityCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).1
    simpa only [zero_add] using h0
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by
    change F halfCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).2
    simpa only [zero_add] using h0
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row25 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 0,modelWord [false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 0,modelWord [false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 17 18 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by
    change F parityCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).1
    simpa only [zero_add] using h0
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by
    change F halfCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).2
    simpa only [zero_add] using h0
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row26 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 0,modelWord [false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 18,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 18 19 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by
    change F parityCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).1
    simpa only [zero_add] using h0
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by
    change F halfCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).2
    simpa only [zero_add] using h0
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row27 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 20,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 19,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 20,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 19 20 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by
    change F parityCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).1
    simpa only [zero_add] using h0
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by
    change F halfCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).2
    simpa only [zero_add] using h0
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row28 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 20,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 21,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 20,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 21,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 20 21 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by
    change F parityCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).1
    simpa only [zero_add] using h0
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by
    change F halfCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).2
    simpa only [zero_add] using h0
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row29 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 21,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 22,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 21,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 22,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 21 22 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by
    change F parityCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).1
    simpa only [zero_add] using h0
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by
    change F halfCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).2
    simpa only [zero_add] using h0
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row30 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 22,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 22,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,(y+y)+(y+y)]]
  have h := leftZero 22 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0 = modelNumeral M 0+modelNumeral M 0 := by
    rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 0) = (0 : M) := by
    change F parityCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).1
    simpa only [zero_add] using h0
  have hh : F halfCode (fun _ => modelNumeral M 0) = modelNumeral M 0 := by
    change F halfCode (fun _ => (0 : M)) = (0 : M)
    have h0 := (modelDouble (0 : M)).2
    simpa only [zero_add] using h0
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h
theorem row31 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row32 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row33 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row34 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row35 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row36 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row37 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [false,true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row38 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [false,true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [true,true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y]]) =
    F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y]]
  have h := rightZero 23 0 23 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 0 = modelNumeral M 0 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
theorem row39 (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,modelWord [true,true,false,false,false,true,false,false,false,false,false,false] x]]) =
    F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,false,false,true,false,false,false,false,false,false] x]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let y := modelWord [true,false,false,false,true,false,false,false,false,false,false] x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 23,F pairCode ![modelNumeral M 0,y+y+1]]) =
    F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,y]]
  have h := rightOne 23 1 24 (by decide) (by decide +kernel) (modelNumeral M 0) y
  have hn : modelNumeral M 0+modelNumeral M 0+modelNumeral M 1 = modelNumeral M 1 := by
    rw [←modelNumeralAdd,←modelNumeralAdd]
  rw [hn] at h
  exact h
def standardRun : Nat → M → M
  | 0, x => x
  | n+1, x => F PackedClock.encodedStep (fun _ => standardRun n x)
theorem standardRunCorrect (n : Nat) (x : M) :
    F PA194Stepper.stepper ![modelNumeral M n,x] = standardRun n x := by
  induction n with
  | zero =>
    change F PA194Stepper.stepper ![F (Code.zero 0) Fin.elim0,x] = _
    rw [PA194Stepper.modelStepperZero]
    rfl
  | succ n ih =>
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M n),x] = _
    rw [PA194Stepper.modelStepperSucc,ih]
    rfl
theorem prefixRun (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 40,F pairCode ![modelNumeral M 24,
      F pairCode ![modelNumeral M 1,modelWord [true,false,false,false,true,false,true,true,true,false,false] x]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,false,false,true,false,false,false,false,false,false] x]] := by
  rw [standardRunCorrect]
  simp only [standardRun]
  rw [row0,row1,row2,row3,row4,row5,row6,row7,row8,row9,row10,row11,row12,row13,row14,row15,row16,row17,row18,row19,row20,row21,row22,row23,row24,row25,row26,row27,row28,row29,row30,row31,row32,row33,row34,row35,row36,row37,row38,row39]
theorem jumpPath30To27 (k f : M) :
    let base := (1 : M)+(f+f)
    let input := modelWord (PA194SourceProgram.path 30) (F zeros ![(k+1)+1,base])
    let output := modelWord (PA194SourceProgram.path 27) (F zeros ![(((k+1)+1)+1)+1,base])
    F PA194Stepper.stepper ![modelNumeral M 40,F pairCode ![modelNumeral M 24,
      F pairCode ![(1 : M),input]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![(1 : M),output]] := by
  dsimp only
  let base := (1 : M)+(f+f)
  let z := F zeros ![k,base]
  have hz1 := modelZerosSucc (M := M) k base
  have hz2 := modelZerosSucc (M := M) (k+1) base
  have hz3 := modelZerosSucc (M := M) ((k+1)+1) base
  have hz4 := modelZerosSucc (M := M) (((k+1)+1)+1) base
  change F zeros ![F Code.succ (fun _ => k),base] = _ at hz1
  change F zeros ![F Code.succ (fun _ => k+1),base] = _ at hz2
  change F zeros ![F Code.succ (fun _ => (k+1)+1),base] = _ at hz3
  change F zeros ![F Code.succ (fun _ => ((k+1)+1)+1),base] = _ at hz4
  rw [←modelAddOne] at hz1 hz2 hz3 hz4
  change F zeros ![k+1,base] = _ at hz1
  change F zeros ![(k+1)+1,base] = _ at hz2
  change F zeros ![((k+1)+1)+1,base] = _ at hz3
  change F zeros ![(((k+1)+1)+1)+1,base] = _ at hz4
  have hi : modelWord (PA194SourceProgram.path 30) (F zeros ![(k+1)+1,base]) =
      modelWord [true,false,false,false,true,false,true,true,true,false,false] z := by
    rw [hz2,hz1,PA194Path30Header.path30]
    rfl
  have ho : modelWord (PA194SourceProgram.path 27) (F zeros ![(((k+1)+1)+1)+1,base]) =
      modelWord [true,false,false,false,true,false,false,false,false,false,false] z := by
    rw [hz4,hz3,hz2,hz1,PA194Path27Header.path27]
    rfl
  rw [hi,ho]
  have h := prefixRun z
  rw [modelNumeralOne] at h
  exact h
#print axioms jumpPath30To27
#print axioms prefixRun
end models
end PA194Site30Jump
