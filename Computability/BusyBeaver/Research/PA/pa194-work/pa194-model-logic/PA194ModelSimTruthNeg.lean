import PA194ModelSimAtomic
import PA194ModelFormulaTranslation
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
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
local instance simTruthNegZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance simTruthNegOne : One M := ⟨F oneCode Fin.elim0⟩
local instance simTruthNegAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance simTruthNegMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance simTruthNegLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance simTruthNegIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem fixedFormulaTranslation_falsum (bound free base reserve : M) :
    F fixedFormulaTranslation ![(^⊥ : M),bound,free,base,reserve] = 1 := by
  have hp : IsUFormula M6.PA.RelationalSource.language (^⊥ : M) := by simp
  rw [fixedFormulaTranslation_correct _ _ _ _ _ hp]
  have h := (formulaReference_recurrence (pair bound free)
    (pair (^⊥ : M) (pair base reserve))).falsum (^⊥ : M)
  change formulaReference _ _ (^⊥ : M) _ = _ at h
  rw [h]
  simp [memValue,impValue,cantor,triangle]

theorem simAxLTruthBody : TargetProvable (impValue (negValue (0 : M)) (impValue (negValue 1) 1)) := by
  let h : Ctx [negValue (1 : M),negValue 0] (negValue 0) := .assumption (by simp)
  exact (Ctx.mp (.closed sequentTruth_zero) h).deduction.deduction.empty

theorem simCutTruthBody : TargetProvable (impValue (impValue (negValue (0 : M)) 1)
    (impValue (impValue (negValue 1) 1) 1)) := by
  let h : Ctx [negValue (negValue (1 : M)),negValue (negValue 0)] (negValue (negValue 1)) := .assumption (by simp)
  exact h.dne.deduction.deduction.empty

theorem simRuleAxL_verum (e : M) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^⊤))
      (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language (^⊤))) 1)) := by
  change TargetProvable (impValue (negatedTranslation e (^⊤))
    (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language (^⊤))) 1))
  rw [neg_verum,negatedTranslation_any,negatedTranslation_any,
    fixedFormulaTranslation_verum,fixedFormulaTranslation_falsum]
  exact simAxLTruthBody

theorem simRuleAxL_falsum (e : M) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^⊥))
      (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language (^⊥))) 1)) := by
  change TargetProvable (impValue (negatedTranslation e (^⊥))
    (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language (^⊥))) 1))
  rw [neg_falsum,negatedTranslation_any,negatedTranslation_any,
    fixedFormulaTranslation_falsum,fixedFormulaTranslation_verum]
  exact tp_mp simAxLTruthBody (imp_exchange _ _ _)

theorem simRuleCut_verum (e : M) :
    numericalQuant.Pr (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (^⊤)) 1)
      (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language (^⊤))) 1) 1)) := by
  change TargetProvable (impValue (impValue (negatedTranslation e (^⊤)) 1)
    (impValue (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language (^⊤))) 1) 1))
  rw [neg_verum,negatedTranslation_any,negatedTranslation_any,
    fixedFormulaTranslation_verum,fixedFormulaTranslation_falsum]
  exact simCutTruthBody

theorem simRuleCut_falsum (e : M) :
    numericalQuant.Pr (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (^⊥)) 1)
      (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language (^⊥))) 1) 1)) := by
  change TargetProvable (impValue (impValue (negatedTranslation e (^⊥)) 1)
    (impValue (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language (^⊥))) 1) 1))
  rw [neg_falsum,negatedTranslation_any,negatedTranslation_any,
    fixedFormulaTranslation_falsum,fixedFormulaTranslation_verum]
  exact tp_mp simCutTruthBody (imp_exchange _ _ _)

#print axioms fixedFormulaTranslation_falsum
#print axioms simRuleAxL_verum
#print axioms simRuleAxL_falsum
#print axioms simRuleCut_verum
#print axioms simRuleCut_falsum
end models
end PA194ModelLogic
