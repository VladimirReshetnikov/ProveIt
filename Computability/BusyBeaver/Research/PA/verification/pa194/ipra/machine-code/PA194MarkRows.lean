import PA194StateOne
import PA194BinaryDouble
set_option autoImplicit false
namespace PA194MarkRows
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

theorem modelMarkEntry (l r : M) :
    (F nextQ ![modelNumeral M 113,l,r+r], F nextL ![modelNumeral M 113,l,r+r],
      F nextR ![modelNumeral M 113,l,r+r]) = (modelNumeral M 14,l+l,r) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 113 < modelNumeral M 194 := modelNumeralStrict 113 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 113,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 113 + modelNumeral M 113 + F parityCode (fun _ => r+r) = modelNumeral M 226 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 226) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 226) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 226) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 226) = _
    rw [modelDirectionNumeral]
    exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M 226) = modelNumeral M 14 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 226) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 113,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 113,l,r+r],F nextL ![modelNumeral M 113,l,r+r],
    F nextR ![modelNumeral M 113,l,r+r]) = stepSem (modelNumeral M 113) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
    change (1 : M) ≠ 0
    exact _root_.one_ne_zero
  simp only [hone,ite_false,add_zero]
theorem modelMarkWrite (l r : M) :
    (F nextQ ![modelNumeral M 14,l,r+r+1], F nextL ![modelNumeral M 14,l,r+r+1],
      F nextR ![modelNumeral M 14,l,r+r+1]) = (modelNumeral M 15,F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 14 < modelNumeral M 194 := modelNumeralStrict 14 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 14,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelOdd r
  have ha : modelNumeral M 14 + modelNumeral M 14 + F parityCode (fun _ => r+r+1) = modelNumeral M 29 := by
    rw [hr.1, ←modelNumeralOne, ←modelNumeralAdd, ←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 29) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 29) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 29) = (0 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 29) = _
    rw [modelDirectionNumeral]
    rfl
  have ht : lookupSem 194 targets (modelNumeral M 29) = modelNumeral M 15 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 29) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 14,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 14,l,r+r+1],F nextL ![modelNumeral M 14,l,r+r+1],
    F nextR ![modelNumeral M 14,l,r+r+1]) = stepSem (modelNumeral M 14) l (r+r+1) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2]
  have hz : (0 : M) = F (Code.zero 0) Fin.elim0 := rfl
  simp only [hz,ite_true]
  simp only [←hz,zero_add,add_assoc]
theorem modelMarkReturn (l r : M) :
    (F nextQ ![modelNumeral M 15,l,r+r], F nextL ![modelNumeral M 15,l,r+r],
      F nextR ![modelNumeral M 15,l,r+r]) = (modelNumeral M 15,F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 15 < modelNumeral M 194 := modelNumeralStrict 15 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 15,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 15 + modelNumeral M 15 + F parityCode (fun _ => r+r) = modelNumeral M 30 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 30) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 30) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 30) = (0 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 30) = _
    rw [modelDirectionNumeral]
    rfl
  have ht : lookupSem 194 targets (modelNumeral M 30) = modelNumeral M 15 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 30) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 15,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 15,l,r+r],F nextL ![modelNumeral M 15,l,r+r],
    F nextR ![modelNumeral M 15,l,r+r]) = stepSem (modelNumeral M 15) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2]
  have hz : (0 : M) = F (Code.zero 0) Fin.elim0 := rfl
  simp only [hz,ite_true]
  simp only [←hz,zero_add,add_assoc]

#print axioms modelMarkEntry
#print axioms modelMarkWrite
#print axioms modelMarkReturn
end models
end PA194MarkRows
