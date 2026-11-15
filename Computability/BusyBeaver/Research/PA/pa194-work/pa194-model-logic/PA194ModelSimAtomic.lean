import PA194ModelSimPropositional
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
local instance simAtomicZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance simAtomicOne : One M := ⟨F oneCode Fin.elim0⟩
local instance simAtomicAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance simAtomicMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance simAtomicLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance simAtomicIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem equalityAtom_polarity (r v bound free reserve : M) :
    F equalityAtomCode ![^nrel (2 : M) r v,bound,free,reserve] =
      F equalityAtomCode ![^rel (2 : M) r v,bound,free,reserve] := by
  simp only [equalityAtomCode,neighborhoodCode_model,PA194TargetStep.app3_model,modelUnary,modelBin,
    modelProjection,modelSucc,modelPairCode,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  simp only [qqRel,qqNRel,modelPredAddOne,pi₁_pair,pi₂_pair]

theorem membershipAtom_polarity (r v bound free reserve : M) :
    F membershipAtomCode ![^nrel (2 : M) r v,bound,free,reserve] =
      F membershipAtomCode ![^rel (2 : M) r v,bound,free,reserve] := by
  simp only [membershipAtomCode,mem_model,PA194TargetStep.app3_model,modelUnary,modelBin,
    modelProjection,modelSucc,modelPairCode,
    modelPi1Code firstProjection firstProjection_certified,
    modelPi2Code secondProjection secondProjection_certified,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  simp only [qqRel,qqNRel,modelPredAddOne,pi₁_pair,pi₂_pair]

theorem boundValue_root (p bound free base reserve : M) :
    boundValue p (pair bound free) (pair p (pair base reserve)) = bound := by
  simp only [boundValue,pi₁_pair,pi₂_pair]
  exact (allocation_root p base bound).1

theorem fixedFormulaTranslation_atom_polarity (r v bound free base reserve : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    F fixedFormulaTranslation ![^nrel (2 : M) r v,bound,free,base,reserve] =
      negValue (F fixedFormulaTranslation ![^rel (2 : M) r v,bound,free,base,reserve]) := by
  have hp : IsUFormula M6.PA.RelationalSource.language (^rel (2 : M) r v) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  have hn : IsUFormula M6.PA.RelationalSource.language (^nrel (2 : M) r v) := by
    simpa only [IsUFormula.nrel] using And.intro hr hv
  rw [fixedFormulaTranslation_correct _ _ _ _ _ hn,
      fixedFormulaTranslation_correct _ _ _ _ _ hp]
  have hpos := (formulaReference_recurrence (pair bound free)
    (pair (^rel (2 : M) r v) (pair base reserve))).positive r v (^rel (2 : M) r v) hr hv
  have hneg := (formulaReference_recurrence (pair bound free)
    (pair (^nrel (2 : M) r v) (pair base reserve))).negative r v (^nrel (2 : M) r v) hr hv
  change formulaReference _ _ (^rel (2 : M) r v) _ = _ at hpos
  change formulaReference _ _ (^nrel (2 : M) r v) _ = _ at hneg
  rw [hpos,hneg]
  simp only [atomValue,boundValue_root,pi₂_pair]
  by_cases he : r = 0
  · simp only [he,ite_true]
    simpa only [qqRel,qqNRel] using congrArg negValue (equalityAtom_polarity 0 v bound free reserve)
  · simp only [he,ite_false]
    simpa only [qqRel,qqNRel] using congrArg negValue (membershipAtom_polarity r v bound free reserve)

theorem simAxLAtomBody (a : M) :
    TargetProvable (impValue (negValue a) (impValue (negValue (negValue a)) 1)) := by
  let A := negValue a
  let B := negValue (negValue a)
  let ha : Ctx [B,A] A := .assumption (by simp)
  let hb : Ctx [B,A] B := .assumption (by simp)
  exact (Ctx.mp hb.dne ha).deduction.deduction.empty

theorem simRuleAxL_positiveAtom (e r v : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^rel (2 : M) r v))
      (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language (^rel (2 : M) r v))) 1)) := by
  change TargetProvable (impValue (negatedTranslation e (^rel (2 : M) r v))
    (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language (^rel (2 : M) r v))) 1))
  rw [neg_rel hr hv,negatedTranslation_any e (^rel (2 : M) r v),
    negatedTranslation_any e (^nrel (2 : M) r v),
    fixedFormulaTranslation_atom_polarity r v _ _ _ _ hr hv]
  exact simAxLAtomBody _

theorem simRuleAxL_negativeAtom (e r v : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^nrel (2 : M) r v))
      (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language (^nrel (2 : M) r v))) 1)) := by
  change TargetProvable (impValue (negatedTranslation e (^nrel (2 : M) r v))
    (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language (^nrel (2 : M) r v))) 1))
  rw [neg_nrel hr hv,negatedTranslation_any e (^rel (2 : M) r v),
    negatedTranslation_any e (^nrel (2 : M) r v),
    fixedFormulaTranslation_atom_polarity r v _ _ _ _ hr hv]
  exact tp_mp (simAxLAtomBody _) (imp_exchange _ _ _)

theorem simCutAtomBody (a : M) :
    TargetProvable (impValue (impValue (negValue a) 1)
      (impValue (impValue (negValue (negValue a)) 1) 1)) := by
  let A := negValue (negValue a)
  let B := negValue A
  let ha : Ctx [B,A] A := .assumption (by simp)
  let hb : Ctx [B,A] B := .assumption (by simp)
  exact (Ctx.mp ha hb).deduction.deduction.empty

theorem simRuleCut_positiveAtom (e r v : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    numericalQuant.Pr (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (^rel (2 : M) r v)) 1)
      (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language (^rel (2 : M) r v))) 1) 1)) := by
  change TargetProvable (impValue (impValue (negatedTranslation e (^rel (2 : M) r v)) 1)
    (impValue (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language (^rel (2 : M) r v))) 1) 1))
  rw [neg_rel hr hv,negatedTranslation_any e (^rel (2 : M) r v),
    negatedTranslation_any e (^nrel (2 : M) r v),
    fixedFormulaTranslation_atom_polarity r v _ _ _ _ hr hv]
  exact simCutAtomBody _

theorem simRuleCut_negativeAtom (e r v : M)
    (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) :
    numericalQuant.Pr (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (^nrel (2 : M) r v)) 1)
      (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language (^nrel (2 : M) r v))) 1) 1)) := by
  change TargetProvable (impValue (impValue (negatedTranslation e (^nrel (2 : M) r v)) 1)
    (impValue (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language (^nrel (2 : M) r v))) 1) 1))
  rw [neg_nrel hr hv,negatedTranslation_any e (^rel (2 : M) r v),
    negatedTranslation_any e (^nrel (2 : M) r v),
    fixedFormulaTranslation_atom_polarity r v _ _ _ _ hr hv]
  exact tp_mp (simCutAtomBody _) (imp_exchange _ _ _)

#print axioms simRuleCut_positiveAtom
#print axioms simRuleCut_negativeAtom
#print axioms simCutAtomBody
#print axioms simRuleAxL_positiveAtom
#print axioms simRuleAxL_negativeAtom
#print axioms simAxLAtomBody
#print axioms fixedFormulaTranslation_atom_polarity
#print axioms equalityAtom_polarity
#print axioms membershipAtom_polarity
#print axioms boundValue_root
end models
end PA194ModelLogic
