import PA194ModelNeighborhoodSpecialization

/-! Target-calculus relation congruence for two translated equality atoms. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance equalityRelExtZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance equalityRelExtOne : One M := ⟨F oneCode Fin.elim0⟩
local instance equalityRelExtAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance equalityRelExtMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance equalityRelExtLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance equalityRelExtIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Two-position congruence of translated equality, valid without freshness. -/
theorem neighborhoodEqualityCongruence_target (a b c d z : M) :
    TargetProvable (impValue (neighborhoodValue a b z)
      (impValue (neighborhoodValue c d z)
        (impValue (neighborhoodValue a c z) (neighborhoodValue b d z)))) := by
  let E₁ := neighborhoodValue a b z
  let E₂ := neighborhoodValue c d z
  let old := neighborhoodValue a c z
  let he₁ : Ctx [old,E₂,E₁] E₁ := .assumption (by simp)
  let he₂ : Ctx [old,E₂,E₁] E₂ := .assumption (by simp)
  let hold : Ctx [old,E₂,E₁] old := .assumption (by simp)
  let hba : Ctx [old,E₂,E₁] (neighborhoodValue b a z) :=
    .mp he₁ (.closed (neighborhood_symm a b z))
  let hbc : Ctx [old,E₂,E₁] (neighborhoodValue b c z) :=
    .mp hold (.mp hba (.closed (neighborhood_trans b a c z)))
  let hbd : Ctx [old,E₂,E₁] (neighborhoodValue b d z) :=
    .mp he₂ (.mp hbc (.closed (neighborhood_trans b c d z)))
  exact hbd.deduction.deduction.deduction.empty

theorem equalityRelExtNNFBody_target (a b c d z : M) :
    let e₁ := neighborhoodValue a b z
    let e₂ := neighborhoodValue c d z
    let old := neighborhoodValue a c z
    let new := neighborhoodValue b d z
    let antecedent := negValue (impValue (negValue (negValue e₁))
      (impValue (negValue (negValue e₂)) (memValue 0 0)))
    TargetProvable (impValue antecedent (impValue (negValue (negValue old)) new)) := by
  dsimp only
  let e₁ := neighborhoodValue a b z
  let e₂ := neighborhoodValue c d z
  let old := neighborhoodValue a c z
  let new := neighborhoodValue b d z
  let S := negValue (impValue (negValue (negValue e₁))
    (impValue (negValue (negValue e₂)) (memValue 0 0)))
  let T := negValue (negValue old)
  let hs : Ctx [T,S] S := .assumption (by simp)
  let ht : Ctx [T,S] T := .assumption (by simp)
  let he₁ : Ctx [T,S] e₁ := hs.negImpLeft.dne
  let he₂ : Ctx [T,S] e₂ := hs.negImpRight.negImpLeft.dne
  let hold : Ctx [T,S] old := ht.dne
  let hnew : Ctx [T,S] new :=
    .mp hold (.mp he₂ (.mp he₁ (.closed (neighborhoodEqualityCongruence_target a b c d z))))
  exact hnew.deduction.deduction.empty

theorem equalityRelExtNNF_supplier (lo z : M) :
    let x₀ := lo
    let x₁ := lo+1
    let x₂ := (lo+1)+1
    let x₃ := ((lo+1)+1)+1
    let e₁ := neighborhoodValue x₃ x₁ z
    let e₂ := neighborhoodValue x₂ x₀ z
    let old := neighborhoodValue x₃ x₂ z
    let new := neighborhoodValue x₁ x₀ z
    let antecedent := negValue (impValue (negValue (negValue e₁))
      (impValue (negValue (negValue e₂)) (memValue 0 0)))
    TargetProvable (allValue x₀ (allValue x₁ (allValue x₂ (allValue x₃
      (impValue antecedent (impValue (negValue (negValue old)) new)))))) := by
  dsimp only
  exact tp_gen lo (tp_gen (lo+1) (tp_gen ((lo+1)+1) (tp_gen (((lo+1)+1)+1)
    (equalityRelExtNNFBody_target (((lo+1)+1)+1) (lo+1) ((lo+1)+1) lo z))))

#print axioms neighborhoodEqualityCongruence_target
#print axioms equalityRelExtNNFBody_target
#print axioms equalityRelExtNNF_supplier
end models
end PA194ModelLogic
