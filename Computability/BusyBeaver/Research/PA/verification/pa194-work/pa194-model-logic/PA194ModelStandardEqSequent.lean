import PA194ModelStandardEqAxioms
import PA194ModelSequentInstance
import PA194ModelFormulaTranslation
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
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
local instance eqAxiomSequentZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqAxiomSequentOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqAxiomSequentAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqAxiomSequentMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqAxiomSequentLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqAxiomSequentIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguageEqAxiomSequent : Language.Eq M6.PA.RelationalSource.language :=
  ⟨M6.PA.RelationalSource.Relation.eq⟩

theorem standardEqAxiom_sseq (bound free base reserve s : M)
    (σ : Sentence M6.PA.RelationalSource.language)
    (hσ : σ ∈ Theory.eqAxiom M6.PA.RelationalSource.language)
    (hz : base + (⌜σ⌝ : M) ≤ reserve) (hp : (⌜σ⌝ : M) ∈ s) :
    TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation
      (pair bound (pair free (pair base reserve))) s 1) :=
  translatedAxiom_sseq bound free base reserve ⌜σ⌝ s hp
    (standardEqAxiom_target bound free base reserve σ hσ hz)

/-- Explicit finite coding of the equality-axiom scheme for this source language. -/
def finiteEqAxiomCode (p : M) : Prop :=
  p = ⌜sourceEqRefl⌝ ∨ p = ⌜sourceEqSymm⌝ ∨ p = ⌜sourceEqTrans⌝ ∨
    p = ⌜sourceEqRelExt⌝ ∨ p = ⌜PA194RelExtTypedTranslation.sourceRelExt⌝

theorem finiteEqAxiomCode_definable : 𝚺₁-Predicate (finiteEqAxiomCode : M → Prop) := by
  unfold finiteEqAxiomCode
  definability

theorem finiteEqAxiomCode_standard (σ : Sentence M6.PA.RelationalSource.language) :
    finiteEqAxiomCode (⌜σ⌝ : M) ↔ σ ∈ Theory.eqAxiom M6.PA.RelationalSource.language := by
  constructor
  · intro h
    rcases h with h | h | h | h | h
    · have hσ : σ = sourceEqRefl := Sentence.quote_inj_iff.mp h
      subst σ; exact Theory.eqAxiom.refl
    · have hσ : σ = sourceEqSymm := Sentence.quote_inj_iff.mp h
      subst σ; exact Theory.eqAxiom.symm
    · have hσ : σ = sourceEqTrans := Sentence.quote_inj_iff.mp h
      subst σ; exact Theory.eqAxiom.trans
    · have hσ : σ = sourceEqRelExt := Sentence.quote_inj_iff.mp h
      subst σ; exact Theory.eqAxiom.relExt (L := M6.PA.RelationalSource.language) M6.PA.RelationalSource.Relation.eq
    · have hσ : σ = PA194RelExtTypedTranslation.sourceRelExt := Sentence.quote_inj_iff.mp h
      subst σ; exact Theory.eqAxiom.relExt (L := M6.PA.RelationalSource.language) M6.PA.RelationalSource.Relation.mem
  · intro hσ
    cases hσ with
    | refl => exact Or.inl rfl
    | symm => exact Or.inr (Or.inl rfl)
    | trans => exact Or.inr (Or.inr (Or.inl rfl))
    | funcExt f => nomatch f
    | relExt r =>
      cases r with
      | eq => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | mem => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

#print axioms finiteEqAxiomCode_definable
#print axioms finiteEqAxiomCode_standard
theorem finiteEqAxiom_sseq (bound free base reserve p s : M)
    (hax : finiteEqAxiomCode p) (hz : base+p ≤ reserve) (hp : p ∈ s) :
    TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation
      (pair bound (pair free (pair base reserve))) s 1) := by
  apply translatedAxiom_sseq bound free base reserve p s hp
  rcases hax with h | h | h | h | h <;> subst p
  · exact fixedFormulaTranslation_eqRefl_target bound free base reserve
  · exact fixedFormulaTranslation_eqSymm_target bound free base reserve
  · exact fixedFormulaTranslation_eqTrans_target bound free base reserve
  · exact fixedFormulaTranslation_eqRelExt_target bound free base reserve
  · exact fixedFormulaTranslation_relExt_target_rootBound bound free base reserve hz

#print axioms finiteEqAxiom_sseq
#print axioms standardEqAxiom_sseq
end models
end PA194ModelLogic
