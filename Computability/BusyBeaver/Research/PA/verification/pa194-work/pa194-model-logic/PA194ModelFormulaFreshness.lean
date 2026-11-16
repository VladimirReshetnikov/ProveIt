import PA194ModelFormulaTranslation

/-! A preliminary reserved-label bound for internally allocated binder labels.
This does not yet establish freshness relative to initial bound or free stacks,
source term occurrences, or semantic preservation of the formula translation. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubAddition
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

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

theorem currentBinder_lt_reserved (b ceiling base reserve : M)
    (hbudget : b+1 ≤ ceiling) (hreserve : base+ceiling ≤ reserve) :
    F labelAtBudget ![b+1,ceiling,base] < reserve := by
  obtain ⟨d,hd⟩ := le_iff_exists_add.mp hbudget
  rw [hd,labelAtBudget_binder]
  have hpos : (0 : M) < b+1 := by simp
  have hless : d < (b+1)+d := by
    simpa only [zero_add,add_zero,add_comm] using add_lt_add_right hpos d
  have hlt : base+d < base+((b+1)+d) := by
    simpa only [add_comm] using add_lt_add_left hless base
  exact lt_of_lt_of_le hlt (by simpa only [hd] using hreserve)

theorem currentBinder_ne_reserved (b ceiling base reserve : M)
    (hbudget : b+1 ≤ ceiling) (hreserve : base+ceiling ≤ reserve) :
    F labelAtBudget ![b+1,ceiling,base] ≠ reserve :=
  ne_of_lt (currentBinder_lt_reserved b ceiling base reserve hbudget hreserve)

#print axioms currentBinder_lt_reserved
#print axioms currentBinder_ne_reserved
end models
end PA194ModelLogic
