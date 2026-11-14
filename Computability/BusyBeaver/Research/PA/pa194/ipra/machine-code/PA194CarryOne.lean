import PA194StateOne
import PA194BinaryDouble
set_option autoImplicit false
namespace PA194CarryOne
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

theorem modelCarryOneEven (l r : M) :
    (F nextQ ![modelNumeral M 1,l,r+r], F nextL ![modelNumeral M 1,l,r+r],
      F nextR ![modelNumeral M 1,l,r+r]) = (modelNumeral M 3,l+l+1,r) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 1 < modelNumeral M 194 := modelNumeralStrict 1 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 1,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 1 + modelNumeral M 1 + F parityCode (fun _ => r+r) = modelNumeral M 2 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 2) = (1 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 2) = _
    rw [modelWriteNumeral]
    exact modelNumeralOne
  have hd : lookupSem 0 directions (modelNumeral M 2) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 2) = _
    rw [modelDirectionNumeral]
    exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M 2) = modelNumeral M 3 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 2) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 1,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 1,l,r+r],F nextL ![modelNumeral M 1,l,r+r],
    F nextR ![modelNumeral M 1,l,r+r]) = stepSem (modelNumeral M 1) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2]
  have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
    change (1 : M) ≠ 0
    exact _root_.one_ne_zero
  simp only [hone,ite_false]
#print axioms modelCarryOneEven
end models
end PA194CarryOne
