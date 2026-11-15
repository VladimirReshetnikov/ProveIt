import PA194OneSpareReturn
import PA194Site28BlankExit
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 12000000
namespace PA194OneSpareRoundTrip
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch PA194OneSpareIterate PA194OneSpareReturn PA194ReturnCell PA194UnaryRuns PA194BinaryDouble PA194StateOne PA194FiniteControls PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem kick (l : M) (hl : F parityCode (fun _ => l) = (1 : M)) :
    let t := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 7,
      F pairCode ![l+l,(1 : M)+(1+1)]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),t+t+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  have h := modelReturnCell (M := M) (0 : M) l (1 : M)
  dsimp only at h
  rw [modelOnesZero,modelOnesZero,hl] at h
  simp only [zero_add] at h
  have hclock : modelNumeral M 2 = (1 : M)+1 := by rw [←modelNumeralOne,←modelNumeralAdd]
  rw [hclock]
  simpa only [add_assoc,add_comm,add_left_comm] using h

theorem roundTrip (n l : M) (hl : F parityCode (fun _ => l) = (1 : M)) :
    let t := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
    let out := F repeatOutput ![n,t]
    F PA194Stepper.stepper ![(n+n)+n,
      F PA194Stepper.stepper ![modelNumeral M 2,
        F PA194Stepper.stepper ![modelNumeral M 3,
          F PA194Stepper.stepper ![(n+n)+n,
            F pairCode ![modelNumeral M 3,F pairCode ![l,F repeatBlock ![n,(0 : M)]]]]]]] =
    F pairCode ![modelNumeral M 7,F pairCode ![F halfCode (fun _ => l),out+out+1]] := by
  dsimp only
  let a := F repeatBlock ![n,l]
  let t := ((1 : M)+1)+((1 : M)+1)+((1 : M)+1)
  have ha : F parityCode (fun _ => a) = (1 : M) := modelRepeatOdd n l hl
  have forward := modelFullCarry n l (0 : M)
  have blank := PA194Site28BlankExit.blankExit a
  have turn := kick a ha
  dsimp only at turn
  have back := modelFullReturn n l t hl
  rw [forward,blank,turn,back]
#print axioms kick
#print axioms roundTrip
end models
end PA194OneSpareRoundTrip
