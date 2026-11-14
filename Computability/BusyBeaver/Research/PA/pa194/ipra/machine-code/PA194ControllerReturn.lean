import PA194MarkerReturnCell
import PA194SeventeenEven
set_option autoImplicit false
namespace PA194ControllerReturn
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194BinaryDouble PA194MarkerReturnCell
open PackedIterationModel ConfigurationStep PRAModelIOpenPairing PA194SeventeenEven
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelPackedSeventeenEven (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 17,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 18,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 17,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 17,l,r+r],F nextL ![TableDispatch.modelNumeral M 17,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 17,l,r+r]) = stepSem (TableDispatch.modelNumeral M 17) l (r+r) at hm
  rw [←hm,modelSeventeenEven]

/-- Return from either marker exit over a run of ones, then cross the
program zero boundary into dense control 18. All values may be nonstandard. -/
theorem modelReturnToControl18 (i : Fin 2) (n l t : M) :
    let a := F ones ![n,(1 : M)+t+t]
    F PA194Stepper.stepper ![((n+1)+1)+1,F pairCode ![TableDispatch.modelNumeral M (returnControl i),
      F pairCode ![F ones ![n,(l+l)+(l+l)],t+t+1]]] =
    F pairCode ![TableDispatch.modelNumeral M 18,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+((a+a)+(a+a))+((a+a)+(a+a))]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let a := F ones ![n,(1 : M)+t+t]
  have hm := modelMarkerReturnCell i n (l+l) t
  dsimp only at hm
  rw [(modelDouble l).1,(modelDouble l).2] at hm
  simp only [zero_add] at hm
  change F PA194Stepper.stepper ![F addCode ![(n+1)+1,F oneCode Fin.elim0],_] = _
  rw [modelAddOne, PA194Stepper.modelStepperSucc,hm]
  change F PackedClock.encodedStep (fun _ => F pairCode ![TableDispatch.modelNumeral M 17,
      F pairCode ![l, (a+a)+(a+a)]]) = _
  rw [show (a+a)+(a+a) = (a+a)+(a+a) by rfl,modelPackedSeventeenEven]
#print axioms modelReturnToControl18
end models
end PA194ControllerReturn
