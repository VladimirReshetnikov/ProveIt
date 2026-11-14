import PA194CarryOne
import PA194CarryThree
import PA194ZeroRuns
set_option autoImplicit false
namespace PA194CarryEntry
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194BinaryDouble PA194CarryOne PA194CarryThree PA194ZeroRuns PackedIterationModel ConfigurationStep PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelPackedCarryOne (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 1,F pairCode ![l,r+r]]) =
    F pairCode ![TableDispatch.modelNumeral M 3,F pairCode ![l+l+1,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 1,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 1,l,r+r],F nextL ![TableDispatch.modelNumeral M 1,l,r+r],
    F nextR ![TableDispatch.modelNumeral M 1,l,r+r]) = stepSem (TableDispatch.modelNumeral M 1) l (r+r) at hm
  rw [←hm,modelCarryOneEven]

theorem modelPackedCarryThree (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 3,F pairCode ![l,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 1,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 3,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 3,l,r+r+1],F nextL ![TableDispatch.modelNumeral M 3,l,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 3,l,r+r+1]) = stepSem (TableDispatch.modelNumeral M 3) l (r+r+1) at hm
  rw [←hm,modelCarryThreeOdd]

#print axioms modelPackedCarryOne
#print axioms modelPackedCarryThree
end models
end PA194CarryEntry
