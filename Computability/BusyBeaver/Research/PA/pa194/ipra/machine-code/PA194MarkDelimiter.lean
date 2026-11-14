import PA194MarkRows
import PA194Stepper
import PackedDecoderModel
set_option autoImplicit false
namespace PA194MarkDelimiter
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PA194MarkRows PA194BinaryDouble PA194StateOne PackedDecoderModel PackedIterationModel ConfigurationStep TableDispatch BinaryTapeCodes PA194FiniteControls
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelPackedEntry (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 113,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 14,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 113,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 113,l,r+r],F nextL ![modelNumeral M 113,l,r+r],
    F nextR ![modelNumeral M 113,l,r+r]) = stepSem (modelNumeral M 113) l (r+r) at hm
  rw [←hm,modelMarkEntry]
theorem modelPackedWrite (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 14,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 14,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 14,l,r+r+1],F nextL ![modelNumeral M 14,l,r+r+1],
    F nextR ![modelNumeral M 14,l,r+r+1]) = stepSem (modelNumeral M 14) l (r+r+1) at hm
  rw [←hm,modelMarkWrite]
theorem modelPackedReturn (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 15,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 15,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 15,l,r+r],F nextL ![modelNumeral M 15,l,r+r],
    F nextR ![modelNumeral M 15,l,r+r]) = stepSem (modelNumeral M 15) l (r+r) at hm
  rw [←hm,modelMarkReturn]
theorem modelMarkDelimiter (l t : M) :
    F PA194Stepper.stepper ![modelNumeral M 3,F pairCode ![modelNumeral M 113,
      F pairCode ![l,(t+t+1)+(t+t+1)]]] =
    F pairCode ![modelNumeral M 15,F pairCode ![F halfCode (fun _ => l),
      F parityCode (fun _ => l)+((t+t)+(t+t))+((t+t)+(t+t))]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  let c := F pairCode ![modelNumeral M 113,F pairCode ![l,(t+t+1)+(t+t+1)]]
  have hs (v : M) : F PA194Stepper.stepper ![v+1,c] =
      F PackedClock.encodedStep (fun _ => F PA194Stepper.stepper ![v,c]) := by
    change F PA194Stepper.stepper ![F addCode ![v,F oneCode Fin.elim0],c] = _
    rw [modelAddOne,PA194Stepper.modelStepperSucc]
  have h0 := PA194Stepper.modelStepperZero c
  change F PA194Stepper.stepper ![(0 : M),c] = c at h0
  have h3 : modelNumeral M 3 = ((0 : M)+1)+1+1 := by
    rw [modelNumeralSucc,modelNumeralSucc,modelNumeralSucc]
    rfl
  rw [h3]
  change F PA194Stepper.stepper ![((0 : M)+1)+1+1,c] = _
  rw [hs,hs,hs,h0]
  dsimp only [c]
  rw [modelPackedEntry,modelPackedWrite,(modelDouble l).1,(modelDouble l).2]
  simp only [zero_add]
  rw [modelPackedReturn]
#print axioms modelMarkDelimiter
end models
end PA194MarkDelimiter
