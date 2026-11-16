import PA194RollbackEleven
import PA194UnaryRuns
set_option autoImplicit false
namespace PA194RollbackTransition
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194BinaryDouble PA194RollbackEleven PA194UnaryRuns PackedIterationModel ConfigurationStep PRAModelIOpenPairing
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelPackedRollbackTransition (l r : M) :
    F PackedClock.encodedStep
      (fun _ => F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![l+l+1,r+r+1]]) =
    F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![l,(r+r+1)+(r+r+1)+1]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![TableDispatch.modelNumeral M 11,l+l+1,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![TableDispatch.modelNumeral M 11,l+l+1,r+r+1],F nextL ![TableDispatch.modelNumeral M 11,l+l+1,r+r+1],
    F nextR ![TableDispatch.modelNumeral M 11,l+l+1,r+r+1]) = stepSem (TableDispatch.modelNumeral M 11) (l+l+1) (r+r+1) at hm
  rw [←hm,modelRollbackElevenOdd]

#print axioms modelPackedRollbackTransition
end models
end PA194RollbackTransition
