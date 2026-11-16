import PA194StateOne
import PA194BinaryDouble
/-! Literal PA194 rows needed for the controller's dense 18–24 segment. -/
set_option autoImplicit false
namespace PA194State18To24
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

theorem modelState18Even (l r : M) :
    (F nextQ ![modelNumeral M 18,l,r+r], F nextL ![modelNumeral M 18,l,r+r],
      F nextR ![modelNumeral M 18,l,r+r]) = (modelNumeral M 19,F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 18 < modelNumeral M 194 := modelNumeralStrict 18 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 18,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 18 + modelNumeral M 18 + F parityCode (fun _ => r+r) = modelNumeral M 36 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 36) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 36) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 36) = (0 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 36) = _
    rw [modelDirectionNumeral]
    rfl
  have ht : lookupSem 194 targets (modelNumeral M 36) = modelNumeral M 19 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 36) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 18,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 18,l,r+r],F nextL ![modelNumeral M 18,l,r+r],
    F nextR ![modelNumeral M 18,l,r+r]) = stepSem (modelNumeral M 18) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hz : (0 : M) = F (Code.zero 0) Fin.elim0 := rfl
  simp only [hz,ite_true]
  simp only [add_assoc]

theorem modelState19Even (l r : M) :
    (F nextQ ![modelNumeral M 19,l,r+r], F nextL ![modelNumeral M 19,l,r+r],
      F nextR ![modelNumeral M 19,l,r+r]) = (modelNumeral M 20,F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 19 < modelNumeral M 194 := modelNumeralStrict 19 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 19,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 19 + modelNumeral M 19 + F parityCode (fun _ => r+r) = modelNumeral M 38 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 38) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 38) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 38) = (0 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 38) = _
    rw [modelDirectionNumeral]
    rfl
  have ht : lookupSem 194 targets (modelNumeral M 38) = modelNumeral M 20 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 38) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 19,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 19,l,r+r],F nextL ![modelNumeral M 19,l,r+r],
    F nextR ![modelNumeral M 19,l,r+r]) = stepSem (modelNumeral M 19) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hz : (0 : M) = F (Code.zero 0) Fin.elim0 := rfl
  simp only [hz,ite_true]
  simp only [add_assoc]

theorem modelState20Even (l r : M) :
    (F nextQ ![modelNumeral M 20,l,r+r], F nextL ![modelNumeral M 20,l,r+r],
      F nextR ![modelNumeral M 20,l,r+r]) = (modelNumeral M 21,F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 20 < modelNumeral M 194 := modelNumeralStrict 20 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 20,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 20 + modelNumeral M 20 + F parityCode (fun _ => r+r) = modelNumeral M 40 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 40) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 40) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 40) = (0 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 40) = _
    rw [modelDirectionNumeral]
    rfl
  have ht : lookupSem 194 targets (modelNumeral M 40) = modelNumeral M 21 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 40) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 20,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 20,l,r+r],F nextL ![modelNumeral M 20,l,r+r],
    F nextR ![modelNumeral M 20,l,r+r]) = stepSem (modelNumeral M 20) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hz : (0 : M) = F (Code.zero 0) Fin.elim0 := rfl
  simp only [hz,ite_true]
  simp only [add_assoc]

theorem modelState21Even (l r : M) :
    (F nextQ ![modelNumeral M 21,l,r+r], F nextL ![modelNumeral M 21,l,r+r],
      F nextR ![modelNumeral M 21,l,r+r]) = (modelNumeral M 22,F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 21 < modelNumeral M 194 := modelNumeralStrict 21 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 21,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 21 + modelNumeral M 21 + F parityCode (fun _ => r+r) = modelNumeral M 42 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 42) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 42) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 42) = (0 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 42) = _
    rw [modelDirectionNumeral]
    rfl
  have ht : lookupSem 194 targets (modelNumeral M 42) = modelNumeral M 22 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 42) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 21,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 21,l,r+r],F nextL ![modelNumeral M 21,l,r+r],
    F nextR ![modelNumeral M 21,l,r+r]) = stepSem (modelNumeral M 21) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hz : (0 : M) = F (Code.zero 0) Fin.elim0 := rfl
  simp only [hz,ite_true]
  simp only [add_assoc]

theorem modelState22Even (l r : M) :
    (F nextQ ![modelNumeral M 22,l,r+r], F nextL ![modelNumeral M 22,l,r+r],
      F nextR ![modelNumeral M 22,l,r+r]) = (modelNumeral M 23,F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 22 < modelNumeral M 194 := modelNumeralStrict 22 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 22,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 22 + modelNumeral M 22 + F parityCode (fun _ => r+r) = modelNumeral M 44 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 44) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 44) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 44) = (0 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 44) = _
    rw [modelDirectionNumeral]
    rfl
  have ht : lookupSem 194 targets (modelNumeral M 44) = modelNumeral M 23 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 44) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 22,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 22,l,r+r],F nextL ![modelNumeral M 22,l,r+r],
    F nextR ![modelNumeral M 22,l,r+r]) = stepSem (modelNumeral M 22) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hz : (0 : M) = F (Code.zero 0) Fin.elim0 := rfl
  simp only [hz,ite_true]
  simp only [add_assoc]

theorem modelState23Even (l r : M) :
    (F nextQ ![modelNumeral M 23,l,r+r], F nextL ![modelNumeral M 23,l,r+r],
      F nextR ![modelNumeral M 23,l,r+r]) = (modelNumeral M 23,l+l,r) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 23 < modelNumeral M 194 := modelNumeralStrict 23 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 23,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelDouble r
  have ha : modelNumeral M 23 + modelNumeral M 23 + F parityCode (fun _ => r+r) = modelNumeral M 46 := by
    rw [hr.1]
    simp only [add_zero]
    rw [←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 46) = (0 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 46) = _
    rw [modelWriteNumeral]
    rfl
  have hd : lookupSem 0 directions (modelNumeral M 46) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 46) = _
    rw [modelDirectionNumeral]
    exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M 46) = modelNumeral M 23 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 46) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 23,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 23,l,r+r],F nextL ![modelNumeral M 23,l,r+r],
    F nextR ![modelNumeral M 23,l,r+r]) = stepSem (modelNumeral M 23) l (r+r) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
    change (1 : M) ≠ 0
    exact _root_.one_ne_zero
  simp only [hone,ite_false,add_zero]

theorem modelState23Odd (l r : M) :
    (F nextQ ![modelNumeral M 23,l,r+r+1], F nextL ![modelNumeral M 23,l,r+r+1],
      F nextR ![modelNumeral M 23,l,r+r+1]) = (modelNumeral M 24,l+l+1,r) := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hq : modelNumeral M 23 < modelNumeral M 194 := modelNumeralStrict 23 194 (by decide)
  have hactive : F ltBitCode ![modelNumeral M 23,modelNumeral M 194] ≠ F (Code.zero 0) Fin.elim0 := by
    intro hz
    exact ((modelLtZero _ _).mp hz) hq
  have hr := modelOdd r
  have ha : modelNumeral M 23 + modelNumeral M 23 + F parityCode (fun _ => r+r+1) = modelNumeral M 47 := by
    rw [hr.1, ←modelNumeralOne, ←modelNumeralAdd, ←modelNumeralAdd]
  have hw : lookupSem 0 writes (modelNumeral M 47) = (1 : M) := by
    rw [←modelLookupAll]
    change F writeCode (fun _ => modelNumeral M 47) = _
    rw [modelWriteNumeral]
    exact modelNumeralOne
  have hd : lookupSem 0 directions (modelNumeral M 47) = (1 : M) := by
    rw [←modelLookupAll]
    change F directionCode (fun _ => modelNumeral M 47) = _
    rw [modelDirectionNumeral]
    exact modelNumeralOne
  have ht : lookupSem 194 targets (modelNumeral M 47) = modelNumeral M 24 := by
    rw [←modelLookupAll]
    change F targetCode (fun _ => modelNumeral M 47) = _
    rw [modelTargetNumeral]
    rfl
  have hn := modelNext (![modelNumeral M 23,l,r+r+1] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hn
  change (F nextQ ![modelNumeral M 23,l,r+r+1],F nextL ![modelNumeral M 23,l,r+r+1],
    F nextR ![modelNumeral M 23,l,r+r+1]) = stepSem (modelNumeral M 23) l (r+r+1) at hn
  rw [hn]
  simp only [stepSem]
  have hadd (a b : M) : F addCode ![a,b] = a+b := rfl
  simp only [hadd,ha,hw,hd,ht,hactive,ite_false,hr.2,zero_add]
  have hone : (1 : M) ≠ F (Code.zero 0) Fin.elim0 := by
    change (1 : M) ≠ 0
    exact _root_.one_ne_zero
  simp only [hone,ite_false,add_zero]

#print axioms modelState18Even
#print axioms modelState19Even
#print axioms modelState20Even
#print axioms modelState21Even
#print axioms modelState22Even
#print axioms modelState23Even
#print axioms modelState23Odd
end models
end PA194State18To24
