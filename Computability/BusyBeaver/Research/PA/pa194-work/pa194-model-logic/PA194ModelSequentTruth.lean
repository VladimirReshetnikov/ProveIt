import PA194ModelSequentInstance
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
local instance sequentTruthZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sequentTruthOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sequentTruthAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sequentTruthMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sequentTruthLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sequentTruthIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sequentTruth_zero : TargetProvable (0 : M) := by
  have h := rho8_provable (0 : M) 0 0 0 (le_refl 0)
  simpa [rho8Value,impValue,cantor,triangle] using h

theorem fixedFormulaTranslation_verum (bound free base reserve : M) :
    F fixedFormulaTranslation ![(^⊤ : M),bound,free,base,reserve] = 0 := by
  have hp : IsUFormula M6.PA.RelationalSource.language (^⊤ : M) := by simp
  rw [fixedFormulaTranslation_correct _ _ _ _ _ hp]
  exact (formulaReference_recurrence _ _).truth _

theorem verumIntro_sseq (bound free base reserve s : M) (h : (^⊤ : M) ∈ s) :
    TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation
      (pair bound (pair free (pair base reserve))) s 1) := by
  apply translatedAxiom_sseq bound free base reserve (^⊤) s h
  rw [fixedFormulaTranslation_verum]
  exact sequentTruth_zero

/-- Weakening of an arbitrary internal finite source set at a fixed environment. -/
theorem weakening_sseq (bound free base reserve s t : M)
    (hsub : ∀ p ∈ s, p ∈ t)
    (hs : TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation
      (pair bound (pair free (pair base reserve))) s 1)) :
    TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation
      (pair bound (pair free (pair base reserve))) t 1) := by
  exact tp_mp hs (ConPA.Sequent.sseq_mono numericalCalc numericalTranslation
    (pair bound (pair free (pair base reserve))) s t 1 hsub)

/-- Conditional form of Foundation's complementary-formula initial sequent.
The caller must supply target-provable incompatibility of the two translations. -/
theorem complementary_sseq (e s p q : M) (hp : p ∈ s) (hq : q ∈ s)
    (hcompat : TargetProvable (impValue (negatedTranslation e p)
      (impValue (negatedTranslation e q) 1))) :
    TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation e s 1) := by
  have hp' := ConPA.Sequent.sseq_mem numericalCalc numericalTranslation e hp
  have hq' := ConPA.Sequent.sseq_mem numericalCalc numericalTranslation e hq
  have hc := ConPA.Sequent.sseq_weaken numericalCalc numericalTranslation hcompat e s
  have h1 := ConPA.Sequent.sseq_mp numericalCalc numericalTranslation hp' hc
  exact ConPA.Sequent.sseq_mp numericalCalc numericalTranslation hq' h1

#print axioms complementary_sseq
#print axioms weakening_sseq
#print axioms sequentTruth_zero
#print axioms fixedFormulaTranslation_verum
#print axioms verumIntro_sseq
end models
end PA194ModelLogic
