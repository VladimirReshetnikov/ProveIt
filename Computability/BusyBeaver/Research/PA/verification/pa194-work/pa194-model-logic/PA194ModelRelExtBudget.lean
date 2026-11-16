import PA194ModelBinaryRelationSubstitution

/-! Reserving the four labels used by the binary relation-extensionality supplier. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance relExtBudgetZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance relExtBudgetOne : One M := ⟨F oneCode Fin.elim0⟩
local instance relExtBudgetAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance relExtBudgetMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance relExtBudgetLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance relExtBudgetIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem relExt_labels_fresh (lo z : M) (hz : ((((lo+1)+1)+1)+1) ≤ z) :
    z ≠ lo ∧ z ≠ lo+1 ∧ z ≠ (lo+1)+1 ∧ z ≠ ((lo+1)+1)+1 := by
  have h3 : ((lo+1)+1)+1 < z := lt_of_lt_of_le (lt_add_one _) hz
  have h2 : (lo+1)+1 < z := lt_trans (lt_add_one _) h3
  have h1 : lo+1 < z := lt_trans (lt_add_one _) h2
  have h0 : lo < z := lt_trans (lt_add_one _) h1
  exact ⟨ne_of_gt h0,ne_of_gt h1,ne_of_gt h2,ne_of_gt h3⟩

theorem relExtNNF_budget_supplier (lo z : M) (hz : ((((lo+1)+1)+1)+1) ≤ z) :
    let x₀ := lo
    let x₁ := lo+1
    let x₂ := (lo+1)+1
    let x₃ := ((lo+1)+1)+1
    let e₁ := neighborhoodValue x₃ x₁ z
    let e₂ := neighborhoodValue x₂ x₀ z
    let old := memValue x₂ x₃
    let new := memValue x₀ x₁
    let antecedent := negValue (impValue (negValue (negValue e₁))
      (impValue (negValue (negValue e₂)) (memValue 0 0)))
    TargetProvable (allValue x₀ (allValue x₁ (allValue x₂ (allValue x₃
      (impValue antecedent (impValue (negValue (negValue old)) new)))))) := by
  obtain ⟨h0,h1,h2,h3⟩ := relExt_labels_fresh lo z hz
  exact relExtNNF_supplier lo z h0 h1 h2 h3

#print axioms relExt_labels_fresh
#print axioms relExtNNF_budget_supplier
end models
end PA194ModelLogic
