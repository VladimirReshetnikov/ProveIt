import PA194Site34PositiveFinish
import PA194Site35To17General
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace PA194Site35RootReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194StateOne PA194FiniteControls PA194BinaryDouble PA194LeftOneWriteOne PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem firstRow (x : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 100,modelWord [true,false] x]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 50,modelWord [false,true,false] x]] := by
  let y := x+x
  change F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 100,y+y+1]]) =
    F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 50,(y+y+1)+(y+y+1)]]
  have h := leftOneWriteOne 17 16 (by decide) (by decide +kernel) (modelNumeral M 100) y
  have hn : modelNumeral M 100 = modelNumeral M 50+modelNumeral M 50 := by rw [←modelNumeralAdd]
  have hp : F parityCode (fun _ => modelNumeral M 100) = (0 : M) := by rw [hn,(modelDouble (modelNumeral M 50)).1]
  have hh : F halfCode (fun _ => modelNumeral M 100) = modelNumeral M 50 := by rw [hn,(modelDouble (modelNumeral M 50)).2] <;> simp only [show modelNumeral M 0 = (0 : M) from rfl,zero_add]
  rw [hp,hh] at h
  simpa only [zero_add,add_assoc,add_comm,add_left_comm] using h

theorem returnWord (x : M) :
    F PA194Stepper.stepper ![modelNumeral M 24,F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 100,modelWord [true,false] x]]] =
    F pairCode ![modelNumeral M 24,F pairCode ![modelNumeral M 1,modelWord [true,false,false,true,false,false,true,false] x]] := by
  have hr := PA194Site34PositiveFinish.returnWord (x+x)
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false] at hr ⊢
  nth_rewrite 1 [show modelNumeral M 24 = F addCode ![modelNumeral M 1,modelNumeral M 23] from by change modelNumeral M 24 = modelNumeral M 1 + modelNumeral M 23; rw [←modelNumeralAdd]]
  rw [PA194StepperCompose.modelStepperCompose]
  have h := firstRow x
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false] at h
  have h1 : F PA194Stepper.stepper ![modelNumeral M 1,
      F pairCode ![modelNumeral M 17,F pairCode ![modelNumeral M 100,modelWord [true,false] x]]] =
      F pairCode ![modelNumeral M 16,F pairCode ![modelNumeral M 50,modelWord [false,true,false] x]] := by
    change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 0),_] = _
    rw [PA194Stepper.modelStepperSucc,
      show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,PA194Stepper.modelStepperZero]
    exact firstRow x
  simp only [modelWord,Bool.false_eq_true,↓reduceIte,Bool.true_eq_false] at h1
  rw [h1,hr]
#print axioms firstRow
#print axioms returnWord
end models
end PA194Site35RootReturn
