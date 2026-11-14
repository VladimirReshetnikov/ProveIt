import PA194TargetHead1Standard
/-! A new single-leaf h1 certificate checker, not the multi-rule upstream
checker or a complete target proof relation. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194Head1Checker
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194NumeralCode PA194CloseVariable PA194TargetCantor

noncomputable def tag : Code 1 := unary firstProjection (.proj 0)
noncomputable def payload : Code 1 := unary secondProjection (.proj 0)
noncomputable def arg1 : Code 1 := unary firstProjection payload
noncomputable def arg2 : Code 1 := unary secondProjection payload
/-- A zero return rejects; a successor returns the head-1 theorem number. -/
noncomputable def check : Code 1 :=
  selectAmong (bin equalityCode tag (numeralCode 1 2))
    (unary .succ (bin machineHead1 arg1 arg2)) (.zero 1)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem field_model (c : M) : F tag ![c] = π₁ c ∧
    F arg1 ![c] = π₁ (π₂ c) ∧ F arg2 ![c] = π₂ (π₂ c) := by
  simp only [tag,arg1,arg2,payload,modelUnary,modelProjection,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified]
  simp only [Matrix.cons_val_zero, and_self]

theorem check_model (c : M) : F check ![c] =
    if π₁ c = 2 then F machineHead1 ![π₁ (π₂ c),π₂ (π₂ c)]+1 else 0 := by
  have h := field_model c
  rw [check,modelChooseEqual,h.1,modelNumeralCode]
  change (if π₁ c = 2 then F (unary .succ (bin machineHead1 arg1 arg2)) ![c]
    else F (.zero 1) ![c]) = _
  rw [PRAMultiplication.modelZero,modelUnary,modelBin,h.2.1,h.2.2,
    PA194TermShiftCodeModel.modelSucc]
  rfl

theorem check_correct (c y : M) : F check ![c] = y+1 ↔ Head1Certificate c y := by
  rw [check_model]
  constructor
  · intro h
    by_cases ht : π₁ c = 2
    · rw [if_pos ht] at h
      have he : F machineHead1 ![π₁ (π₂ c),π₂ (π₂ c)] = y := add_right_cancel h
      refine ⟨π₁ (π₂ c),π₂ (π₂ c), ?_, he.symm⟩
      rw [pair_unpair, ← ht, pair_unpair]
    · rw [if_neg ht] at h
      exact False.elim (zero_ne_add_one y h)
  · rintro ⟨a,b,rfl,rfl⟩
    simp

#print axioms check_correct
#print axioms check_model
end models
end PA194Head1Checker
