import DiophantineConsistency.PRAPeanoMinusMulComm
import DiophantineConsistency.PRAEqualityDifference

/-! Basic strict-order axioms of Foundation PA-minus inside candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPeanoMinusOrderBasic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAAdditionZeroLeft
  PRAQCompatibility PRAQOrder PRAExhaustion PRASubAddition PRAEqualityDifference PRABooleanOps PRAPeanoMinusBasic

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
private def succ (x : M) : M := Structure.func (L := language) Code.succ (fun _ => x)
private def sub (x y : M) : M := Structure.func (L := language) subCode ![x,y]

private theorem addZero (x : M) : x + 0 = x := modelAddZero x
private theorem zeroAdd (x : M) : (0 : M) + x = x := modelZeroLeft x
private theorem oneSuccZero : (1 : M) = succ 0 := modelOneSuccZero
private theorem succAdd (x y : M) : succ x + y = succ (x+y) := PRAAdditionSuccLeft.modelSuccLeft x y

theorem ltWitness (x y : M) : x < y ↔ ∃ c, x + succ c = y := modelLtWitness x y

theorem ltDifference (x y : M) : x < y ↔ sub y x ≠ 0 := modelLtDifference x y

theorem modelLtIrrefl (x : M) : ¬x < x := by
  rw [ltDifference]
  have h := modelSubAdd x (0 : M)
  change sub (x + 0) x = 0 at h
  rw [addZero] at h
  exact not_not_intro h

theorem modelLtTri (x y : M) : x < y ∨ x = y ∨ y < x := by
  by_cases hxy : sub y x = 0
  · by_cases hyx : sub x y = 0
    · right; left
      exact modelBothDifferencesZero x y hyx hxy
    · right; right
      exact (ltDifference y x).mpr hyx
  · left
    exact (ltDifference x y).mpr hxy

theorem modelZeroLe (x : M) : (0 : M) < x ∨ (0 : M) = x := by
  by_cases hx : x = 0
  · exact Or.inr hx.symm
  · have hs := (modelZeroOrSuccPred x).resolve_left hx
    left
    apply (ltWitness 0 x).mpr
    refine ⟨Structure.func (L := language) predCode (fun _ => x), ?_⟩
    change (0 : M) + succ (Structure.func (L := language) predCode (fun _ => x)) = x
    rw [zeroAdd]
    exact hs

theorem modelZeroLtOne : (0 : M) < 1 := by
  apply (ltWitness 0 1).mpr
  refine ⟨0, ?_⟩
  rw [zeroAdd]
  exact oneSuccZero.symm

theorem modelOneLeOfZeroLt (x : M) (hx : (0 : M) < x) : (1 : M) < x ∨ (1 : M) = x := by
  obtain ⟨c,hc⟩ := (ltWitness 0 x).mp hx
  rw [zeroAdd] at hc
  by_cases hc0 : c = 0
  · right
    rw [hc0] at hc
    exact oneSuccZero.trans hc
  · have hs := (modelZeroOrSuccPred c).resolve_left hc0
    change succ (Structure.func (L := language) predCode (fun _ => c)) = c at hs
    left
    apply (ltWitness 1 x).mpr
    refine ⟨Structure.func (L := language) predCode (fun _ => c), ?_⟩
    change (1 : M) + succ (Structure.func (L := language) predCode (fun _ => c)) = x
    rw [hs]
    rw [oneSuccZero, succAdd, zeroAdd]
    exact hc

theorem modelAddEqOfLt (x y : M) (h : x < y) : ∃ z, x + z = y := by
  obtain ⟨c,hc⟩ := (ltWitness x y).mp h
  exact ⟨succ c,hc⟩

theorem modelMappedAddEqOfLt : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.addEqOfLt := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.addEqOfLt]
  intro x y h
  exact modelAddEqOfLt x y h

theorem modelMappedZeroLe : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.zeroLe := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.zeroLe]
  intro x
  simpa [Semiformula.Operator.LE.def_of_Eq_of_LT, Semiformula.val_operator_or, Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.val, or_comm] using (modelZeroLe x)

theorem modelMappedZeroLtOne : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.zeroLtOne := by
  apply mapped_of_standard
  simpa [PeanoMinus.Axiom.zeroLtOne] using (modelZeroLtOne (M := M))

theorem modelMappedOneLeOfZeroLt : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.oneLeOfZeroLt := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.oneLeOfZeroLt]
  intro x h
  simpa [Semiformula.Operator.LE.def_of_Eq_of_LT, Semiformula.val_operator_or, Semiformula.Operator.Eq.sentence_eq, Semiformula.Operator.LT.sentence_eq, Semiformula.Operator.val, or_comm] using (modelOneLeOfZeroLt x h)

theorem modelMappedLtIrrefl : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.ltIrrefl := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.ltIrrefl]
  exact modelLtIrrefl

theorem modelMappedLtTri : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.ltTri := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.ltTri]
  exact modelLtTri

end models

theorem PRA_proves_addEqOfLt : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addEqOfLt := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedAddEqOfLt

theorem PRA_proves_zeroLe : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.zeroLe := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedZeroLe

theorem PRA_proves_zeroLtOne : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.zeroLtOne := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedZeroLtOne

theorem PRA_proves_oneLeOfZeroLt : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.oneLeOfZeroLt := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedOneLeOfZeroLt

theorem PRA_proves_ltIrrefl : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.ltIrrefl := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedLtIrrefl

theorem PRA_proves_ltTri : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.ltTri := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedLtTri

end DiophantineConsistency.PRAPeanoMinusOrderBasic
