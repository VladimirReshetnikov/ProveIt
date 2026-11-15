import PA194ModelFiniteEqTheory
import PA194ModelSequentTruth
import ConPADerivation
import PA194ModelFormulaTranslation
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.HierarchySymbol.Semiformula
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance simAxiomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance simAxiomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance simAxiomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance simAxiomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance simAxiomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance simAxiomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguageSimAxiom : Language.Eq M6.PA.RelationalSource.language :=
  ⟨M6.PA.RelationalSource.Relation.eq⟩

noncomputable def simBound (e : M) : M := π₁ e
noncomputable def simFree (e : M) : M := π₁ (π₂ e)
noncomputable def simBase (e : M) : M := π₁ (π₂ (π₂ e))
noncomputable def simReserve (e : M) : M := π₂ (π₂ (π₂ e))

theorem negatedTranslation_any (e p : M) :
    negatedTranslation e p = negValue (F fixedFormulaTranslation
      ![p,simBound e,simFree e,simBase e,simReserve e]) := by
  have h := negatedTranslation_model (simBound e) (simFree e) (simBase e) (simReserve e) p
  simpa [simBound,simFree,simBase,simReserve,pair_unpair] using h

theorem positiveTarget_rule (e p : M)
    (hprov : TargetProvable (F fixedFormulaTranslation
      ![p,simBound e,simFree e,simBase e,simReserve e])) :
    TargetProvable (impValue (negatedTranslation e p) 1) := by
  rw [negatedTranslation_any]
  let A := F fixedFormulaTranslation ![p,simBound e,simFree e,simBase e,simReserve e]
  let ha : Ctx [negValue A] A := .closed hprov
  let hn : Ctx [negValue A] (negValue A) := .assumption (by simp)
  exact (Ctx.mp ha hn).deduction.empty

theorem finiteEqTheory_axiom_rule (e p : M) (hz : simBase e + p ≤ simReserve e) :
    letI := finiteEqTheoryDelta
    p ∈ (Theory.eqAxiom M6.PA.RelationalSource.language).Δ₁Class →
    TargetProvable (impValue (negatedTranslation e p) 1) := by
  letI := finiteEqTheoryDelta
  intro hax
  apply positiveTarget_rule
  have hf := (finiteEqTheory_class p).mp hax
  rcases hf with h | h | h | h | h <;> subst p
  · exact fixedFormulaTranslation_eqRefl_target _ _ _ _
  · exact fixedFormulaTranslation_eqSymm_target _ _ _ _
  · exact fixedFormulaTranslation_eqTrans_target _ _ _ _
  · exact fixedFormulaTranslation_eqRelExt_target _ _ _ _
  · exact fixedFormulaTranslation_relExt_target_rootBound _ _ _ _ hz

theorem verumIntro_rule (e : M) : TargetProvable (impValue (negatedTranslation e (^⊤)) 1) := by
  apply positiveTarget_rule
  rw [fixedFormulaTranslation_verum]
  exact sequentTruth_zero

/-- Concrete target-calculus conclusion required by `Sim.ruleVerum`. -/
theorem simRuleVerum (e : M) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^⊤)) 1) := by
  exact verumIntro_rule e

/-- Concrete equality-theory conclusion required by `Sim.ruleAxm`; the
reserve estimate must be provided by the eventual admissibility invariant. -/
theorem simRuleEqAxiom (e p : M) (hz : simBase e + p ≤ simReserve e) :
    letI := finiteEqTheoryDelta
    p ∈ (Theory.eqAxiom M6.PA.RelationalSource.language).Δ₁Class →
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1) := by
  exact finiteEqTheory_axiom_rule e p hz

#print axioms simRuleVerum
#print axioms simRuleEqAxiom
#print axioms negatedTranslation_any
#print axioms positiveTarget_rule
#print axioms finiteEqTheory_axiom_rule
#print axioms verumIntro_rule
end models
end PA194ModelLogic
