import PA194StateOne
import PA194BinaryDouble
set_option autoImplicit false
namespace PA194RollbackEleven
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRABooleanOps PRAIsZero
open BinaryTapeCodes TableDispatch TableModelSemantics ConfigurationStep PackedRootModel PA194FiniteControls PA194StateOne PA194BinaryDouble

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelRollbackElevenOdd (l r : M) :
    (F nextQ ![modelNumeral M 11,l+l+1,r+r+1], F nextL ![modelNumeral M 11,l+l+1,r+r+1],
      F nextR ![modelNumeral M 11,l+l+1,r+r+1]) = (modelNumeral M 11,l,(r+r+1)+(r+r+1)+1) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 11 < modelNumeral M 194 := modelNumeralStrict 11 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 11,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelOdd r
  have hl := modelOdd l
  have ha : modelNumeral M 11 + modelNumeral M 11 + F parityCode (fun _ => r+r+1) = modelNumeral M 23 := by
    rw [hr.1, ←modelNumeralOne, ←modelNumeralAdd, ←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 23) = (1 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 23) = _
    rw [modelWriteNumeral]
    exact modelNumeralOne
  have hd : lookupSem 0 directions (modelNumeral M 23) = (0 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 23) = _
    rw [modelDirectionNumeral]
    rfl
  have ht : lookupSem 194 targets (modelNumeral M 23) = modelNumeral M 11 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 23) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 11,l+l+1,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 11,l+l+1,r+r+1],F nextL ![modelNumeral M 11,l+l+1,r+r+1],
    F nextR ![modelNumeral M 11,l+l+1,r+r+1]) = stepSem (modelNumeral M 11) (l+l+1) (r+r+1) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hl.1,hl.2,hr.2]
  have hz : (0 : M) = F (Code.zero 0) Fin.elim0 := rfl
  simp only [hz,ite_true]
  simp only [add_assoc, add_left_comm, add_comm]
#print axioms modelRollbackElevenOdd
end models
end PA194RollbackEleven
