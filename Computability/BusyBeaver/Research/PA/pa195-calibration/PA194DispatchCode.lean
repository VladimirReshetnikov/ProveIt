import PA194TagDecoder
import PA194NumeralCode
import DiophantineConsistency.PRAEqualityCode
import DiophantineConsistency.PRASelectCode

/-! Primitive-recursive dispatch for the four PA194 source tags and zero alias. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194DispatchCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAEqualityCode PRASelectCode PRABooleanOps
  PA194NumeralCode PA194TagDecoder

def equalTest (x y : Code 1) : Code 1 := bin equalityCode x y
def tagIs (tag : Code 1) (k : Nat) : Code 1 := equalTest tag (numeralCode 1 k)
def dispatchCode (tag truth implication membership universal equality : Code 1) : Code 1 :=
  selectAmong (equalTest (.proj 0) (.zero 1)) truth
    (selectAmong (tagIs tag 1) membership
      (selectAmong (tagIs tag 2) universal
        (selectAmong (tagIs tag 3) equality implication)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelChooseEq (x y yes no : Code 1) (n : M) :
    Structure.func (L := language) (selectAmong (equalTest x y) yes no) (fun _ => n) =
      if Structure.func (L := language) x (fun _ => n) = Structure.func (L := language) y (fun _ => n)
      then Structure.func (L := language) yes (fun _ => n)
      else Structure.func (L := language) no (fun _ => n) := by
  rw [modelSelectAmong,equalTest,modelBin]
  have hb := modelEqualityCode (Structure.func (L := language) x (fun _ => n))
    (Structure.func (L := language) y (fun _ => n))
  by_cases he : Structure.func (L := language) x (fun _ => n) = Structure.func (L := language) y (fun _ => n)
  · have hone := hb.2.mpr he
    simp only [he] at hone
    simp only [he, if_pos]
    rw [hone]
    exact modelSelectOne _ _
  · simp only [he, if_false]
    have hz : Structure.func (L := language) equalityCode
        ![Structure.func (L := language) x (fun _ => n), Structure.func (L := language) y (fun _ => n)] =
          Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
      rcases hb.1 with hz | ho
      · exact hz
      · exact False.elim (he (hb.2.mp ho))
    rw [hz]
    exact modelSelectZero _ _

theorem modelDispatch (tag truth implication membership universal equality : Code 1) (n : M) :
    Structure.func (L := language) (dispatchCode tag truth implication membership universal equality) (fun _ => n) =
      if n = 0 then Structure.func (L := language) truth (fun _ => n)
      else if Structure.func (L := language) tag (fun _ => n) = ((1 : Nat) : M) then Structure.func (L := language) membership (fun _ => n)
      else if Structure.func (L := language) tag (fun _ => n) = ((2 : Nat) : M) then Structure.func (L := language) universal (fun _ => n)
      else if Structure.func (L := language) tag (fun _ => n) = ((3 : Nat) : M) then Structure.func (L := language) equality (fun _ => n)
      else Structure.func (L := language) implication (fun _ => n) := by
  rw [dispatchCode,modelChooseEq]
  rw [modelProjection,PRAMultiplication.modelZero]
  change (if n = 0 then _ else _) = _
  split
  · rfl
  · simp only [tagIs]
    rw [modelChooseEq,modelNumeralCode]
    split
    · rfl
    · rw [modelChooseEq,modelNumeralCode]
      split
      · rfl
      · rw [modelChooseEq,modelNumeralCode]
/-- With a certified source-tag code, dispatch has its exact remainder-based
semantics for all model source values. -/
theorem modelDispatchTagged (tag truth implication membership universal equality : Code 1)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag) (n : M) :
    Structure.func (L := language) (dispatchCode tag truth implication membership universal equality) (fun _ => n) =
      if n = 0 then Structure.func (L := language) truth (fun _ => n)
      else if n % 4 = ((1 : Nat) : M) then Structure.func (L := language) membership (fun _ => n)
      else if n % 4 = ((2 : Nat) : M) then Structure.func (L := language) universal (fun _ => n)
      else if n % 4 = ((3 : Nat) : M) then Structure.func (L := language) equality (fun _ => n)
      else Structure.func (L := language) implication (fun _ => n) := by
  rw [modelDispatch,modelTagCode tag htag]

/-- Zero is selected as truth, independently of its implication-tag alias. -/
theorem modelDispatchZero (tag truth implication membership universal equality : Code 1) :
    Structure.func (L := language) (dispatchCode tag truth implication membership universal equality) (fun _ => (0 : M)) =
      Structure.func (L := language) truth (fun _ => (0 : M)) := by
  rw [modelDispatch]
  simp

/-- A tag-1 source constructor selects the supplied membership branch. -/
theorem modelDispatchMembership (tag truth implication membership universal equality : Code 1)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag) (payload : M) :
    Structure.func (L := language) (dispatchCode tag truth implication membership universal equality)
      (fun _ => 4 * payload + 1) = Structure.func (L := language) membership (fun _ => 4 * payload + 1) := by
  rw [modelDispatchTagged tag truth implication membership universal equality htag]
  have hn : 4 * payload + 1 ≠ (0 : M) := by
    have hp : (0 : M) < 4 * payload + 1 := by simp
    exact ne_of_gt hp
  have hm : (4 * payload + 1) % 4 = ((1 : Nat) : M) := by
    simpa only [mul_comm, Nat.cast_one] using (mod_mul_add_of_lt payload 4 (show (1 : M) < 4 by norm_num))
  simp only [hn, if_false, hm, if_true]

/-- A tag-3 source constructor selects the supplied equality branch. -/
theorem modelDispatchEquality (tag truth implication membership universal equality : Code 1)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag) (payload : M) :
    Structure.func (L := language) (dispatchCode tag truth implication membership universal equality)
      (fun _ => 4 * payload + 3) = Structure.func (L := language) equality (fun _ => 4 * payload + 3) := by
  rw [modelDispatchTagged tag truth implication membership universal equality htag]
  have hn : 4 * payload + 3 ≠ (0 : M) := by
    have hp : (0 : M) < 4 * payload + 3 := by simp
    exact ne_of_gt hp
  have hm : (4 * payload + 3) % 4 = ((3 : Nat) : M) := by
    simpa only [mul_comm, Nat.cast_ofNat] using (mod_mul_add_of_lt payload 4 (show (3 : M) < 4 by norm_num))
  have h31 : ((3 : Nat) : M) ≠ ((1 : Nat) : M) := by norm_num
  have h32 : ((3 : Nat) : M) ≠ ((2 : Nat) : M) := by norm_num
  simp only [hn, if_false, hm, h31, h32, if_true]

/-- A tag-2 source constructor selects the supplied universal branch. -/
theorem modelDispatchUniversal (tag truth implication membership universal equality : Code 1)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag) (payload : M) :
    Structure.func (L := language) (dispatchCode tag truth implication membership universal equality)
      (fun _ => 4 * payload + 2) = Structure.func (L := language) universal (fun _ => 4 * payload + 2) := by
  rw [modelDispatchTagged tag truth implication membership universal equality htag]
  have hn : 4 * payload + 2 ≠ (0 : M) := by
    have hp : (0 : M) < 4 * payload + 2 := by simp
    exact ne_of_gt hp
  have hm : (4 * payload + 2) % 4 = ((2 : Nat) : M) := by
    simpa only [mul_comm, Nat.cast_ofNat] using (mod_mul_add_of_lt payload 4 (show (2 : M) < 4 by norm_num))
  have h21 : ((2 : Nat) : M) ≠ ((1 : Nat) : M) := by norm_num
  simp only [hn, if_false, hm, h21, if_true]

/-- A nonzero tag-0 constructor selects implication; the zero alias selects
truth by `modelDispatchZero`. -/
theorem modelDispatchImplication (tag truth implication membership universal equality : Code 1)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag) (payload : M)
    (hn : 4 * payload ≠ 0) :
    Structure.func (L := language) (dispatchCode tag truth implication membership universal equality)
      (fun _ => 4 * payload) = Structure.func (L := language) implication (fun _ => 4 * payload) := by
  rw [modelDispatchTagged tag truth implication membership universal equality htag]
  have hm : (4 * payload) % 4 = (0 : M) := by simp
  have h01 : (0 : M) ≠ ((1 : Nat) : M) := by norm_num
  have h02 : (0 : M) ≠ ((2 : Nat) : M) := by norm_num
  have h03 : (0 : M) ≠ ((3 : Nat) : M) := by norm_num
  simp only [hn, if_false, hm, h01, h02, h03]

end models
#print axioms modelDispatchImplication
#print axioms modelDispatchUniversal
#print axioms modelDispatchEquality
#print axioms modelDispatchMembership
#print axioms modelDispatchTagged
#print axioms modelDispatchZero
#print axioms modelChooseEq
#print axioms modelDispatch
end PA194DispatchCode
