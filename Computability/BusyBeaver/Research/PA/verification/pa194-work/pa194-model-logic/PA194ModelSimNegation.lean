import PA194ModelDualInduction
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
local instance simNegationZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance simNegationOne : One M := ⟨F oneCode Fin.elim0⟩
local instance simNegationAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance simNegationMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance simNegationLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance simNegationIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem targetDual_axl (a n : M) (h : TargetDual a n) :
    TargetProvable (impValue (negValue a) (impValue (negValue n) 1)) := by
  let ha : Ctx [negValue n,negValue a] (negValue a) := .assumption (by simp)
  let hn : Ctx [negValue n,negValue a] (negValue n) := .assumption (by simp)
  let hpos : Ctx [negValue n,negValue a] n := Ctx.mp ha (.closed h.2)
  exact (Ctx.mp hpos hn).deduction.deduction.empty

theorem targetDual_cut (a n : M) (h : TargetDual a n) :
    TargetProvable (impValue (impValue (negValue a) 1)
      (impValue (impValue (negValue n) 1) 1)) := by
  let ha : Ctx [negValue (negValue n),negValue (negValue a)] (negValue (negValue a)) := .assumption (by simp)
  let hn : Ctx [negValue (negValue n),negValue (negValue a)] (negValue (negValue n)) := .assumption (by simp)
  let hnotn : Ctx [negValue (negValue n),negValue (negValue a)] (negValue n) :=
    Ctx.mp ha (.closed (contrapose h.1))
  exact (Ctx.mp hnotn hn).deduction.deduction.empty

theorem simRuleAxL (e s p : M)
    (hs : IsFormulaSet M6.PA.RelationalSource.language s) (hp : p ∈ s) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p)
      (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language p)) 1)) := by
  have hv : IsUFormula M6.PA.RelationalSource.language p := (hs _ hp).isUFormula
  have hdual := translationDual_all_codes p (simBound e) (simFree e) (simBase e) (simReserve e) hv
  unfold TranslationDual at hdual
  change TargetProvable (impValue (negatedTranslation e p)
    (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language p)) 1))
  rw [negatedTranslation_any,negatedTranslation_any]
  exact targetDual_axl _ _ hdual

theorem simRuleCut_valid (e p : M) (hp : IsUFormula M6.PA.RelationalSource.language p) :
    numericalQuant.Pr (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e p) 1)
      (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language p)) 1) 1)) := by
  have hdual := translationDual_all_codes p (simBound e) (simFree e) (simBase e) (simReserve e) hp
  unfold TranslationDual at hdual
  change TargetProvable (impValue (impValue (negatedTranslation e p) 1)
    (impValue (impValue (negatedTranslation e (neg M6.PA.RelationalSource.language p)) 1) 1))
  rw [negatedTranslation_any,negatedTranslation_any]
  exact targetDual_cut _ _ hdual

/-- The validity premise follows from an actual first cut-premise derivation. -/
theorem simRuleCut_of_derivation (e s p d : M)
    (T : Theory M6.PA.RelationalSource.language) [T.Δ₁]
    (hd : DerivationOf T d (insert p s)) :
    numericalQuant.Pr (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e p) 1)
      (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e (neg M6.PA.RelationalSource.language p)) 1) 1)) := by
  have hv : IsFormula M6.PA.RelationalSource.language p :=
    (IsFormulaSet.insert_iff.mp hd.isFormulaSet).1
  exact simRuleCut_valid e p hv.isUFormula

#print axioms simRuleCut_of_derivation
#print axioms simRuleAxL
#print axioms simRuleCut_valid
#print axioms targetDual_axl
#print axioms targetDual_cut
end models
end PA194ModelLogic
