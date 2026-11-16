import PA194ADOrdinary
import PA194FiniteControls
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PA194ADDispatch
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne TableDispatch PRAModelIOpenPairing

def writes : List Nat := PA194ADTable.adRows.map (fun r => r.1)
def directions : List Nat := PA194ADTable.adRows.map (fun r => r.2.1)
def targets : List Nat := PA194ADTable.adRows.map (fun r => r.2.2)
def writeCode : Code 1 := lookupCode 0 writes
def directionCode : Code 1 := lookupCode 0 directions
def targetCode : Code 1 := lookupCode 194 targets

theorem writes_eq : writes = TableDispatch.writes := by decide +kernel
theorem directions_eq : directions = TableDispatch.directions := by decide +kernel
theorem writeCode_eq : writeCode = TableDispatch.writeCode := by rw [writeCode, writes_eq, TableDispatch.writeCode]
theorem directionCode_eq : directionCode = TableDispatch.directionCode := by rw [directionCode, directions_eq, TableDispatch.directionCode]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem modelTargetNumeral (i : Nat) :
    F targetCode (fun _ => modelNumeral M i) =
      modelNumeral M (PA194ADTable.adRows.getD i (0,0,194)).2.2 := by
  change F (lookupCode 194 targets) _ = _
  rw [modelLookupNumeral]
  have h := getDMap (fun r : Nat × Nat × Nat => r.2.2) PA194ADTable.adRows i (0,0,194)
  change targets.getD i 194 = _ at h
  exact congrArg (modelNumeral M) h

theorem modelTargetNumeral_eq (i : Nat) (h₁ : i ≠ 219) (h₂ : i ≠ 221) (h₃ : i ≠ 249) :
    F targetCode (fun _ => modelNumeral M i) =
      F TableDispatch.targetCode (fun _ => modelNumeral M i) := by
  rw [modelTargetNumeral, TableDispatch.modelTargetNumeral,
    PA194ADTable.ordinary_rows i h₁ h₂ h₃]

theorem modelTarget_eq_of_below (x : M) (hx : x < modelNumeral M 388)
    (h₁ : x ≠ modelNumeral M 219) (h₂ : x ≠ modelNumeral M 221)
    (h₃ : x ≠ modelNumeral M 249) :
    F targetCode (fun _ => x) = F TableDispatch.targetCode (fun _ => x) := by
  obtain ⟨i, hi⟩ := PA194FiniteControls.modelBelowNumeral 388 x hx
  have g₁ : i.val ≠ 219 := by intro h; apply h₁; rw [hi,h]
  have g₂ : i.val ≠ 221 := by intro h; apply h₂; rw [hi,h]
  have g₃ : i.val ≠ 249 := by intro h; apply h₃; rw [hi,h]
  rw [hi]
  exact modelTargetNumeral_eq i.val g₁ g₂ g₃

theorem modified_targets :
    F targetCode (fun _ => modelNumeral M 219) = modelNumeral M 114 ∧
    F targetCode (fun _ => modelNumeral M 221) = modelNumeral M 114 ∧
    F targetCode (fun _ => modelNumeral M 249) = modelNumeral M 95 := by
  rw [modelTargetNumeral, modelTargetNumeral, modelTargetNumeral]
  exact ⟨rfl, rfl, rfl⟩

#print axioms modified_targets
#print axioms modelTarget_eq_of_below
#print axioms modelTargetNumeral
#print axioms modelTargetNumeral_eq
end models
#print axioms writes_eq
#print axioms directions_eq
#print axioms writeCode_eq
#print axioms directionCode_eq
end PA194ADDispatch
