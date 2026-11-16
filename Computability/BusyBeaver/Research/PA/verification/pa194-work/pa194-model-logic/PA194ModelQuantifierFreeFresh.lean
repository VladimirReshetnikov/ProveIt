import PA194ModelBelowFreshInduction
import PA194ModelDescendantComplexity
import PA194ModelRankedEnvironment
import PA194ModelDualInduction
import PA194ModelAtomicFreshness
import PA194RelExtTypedTranslation

/-! Internal structural induction for arbitrary-label vacuity. -/
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
local instance qfShiftZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance qfShiftOne : One M := ⟨F oneCode Fin.elim0⟩
local instance qfShiftAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance qfShiftMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance qfShiftLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance qfShiftIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]





/-- No binder node is reachable by an internally coded constructor chain. -/
def InternalQuantifierFree (p : M) : Prop :=
  ¬ ∃ a : M, CodedSyntacticDescendant p (^∀ a) ∨ CodedSyntacticDescendant p (^∃ a)

theorem internalQuantifierFree_definable : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := by
  haveI : 𝚺₁-Relation (CodedSyntacticDescendant (M := M)) := codedSyntacticDescendant_definable
  unfold InternalQuantifierFree
  definability

theorem internalQuantifierFree_child (parent child bit : M)
    (he : SourceDirectEdge parent child bit) (h : InternalQuantifierFree parent) :
    InternalQuantifierFree child := by
  intro ⟨a,ha⟩
  apply h
  refine ⟨a,?_⟩
  rcases ha with ha | ha
  · exact Or.inl (codedSyntacticDescendant_extend parent child (^∀ a) bit he ha)
  · exact Or.inr (codedSyntacticDescendant_extend parent child (^∃ a) bit he ha)

theorem internalQuantifierFree_not_all (a : M) : ¬ InternalQuantifierFree (^∀ a) := by
  intro h
  exact h ⟨a,Or.inl (codedSyntacticDescendant_self _)⟩

theorem internalQuantifierFree_not_ex (a : M) : ¬ InternalQuantifierFree (^∃ a) := by
  intro h
  exact h ⟨a,Or.inr (codedSyntacticDescendant_self _)⟩

/-- A syntactic leaf remains stationary for every model-valued path length. -/
theorem sourcePath_leaf_stationary (tag payload choices n : M)
    (ht : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3) :
    F sourcePath ![n,pair tag payload+1,choices] = pair tag payload+1 := by
  haveI : 𝚺₁-Function₁ (fun k : M => F sourcePath ![k,pair tag payload+1,choices]) :=
    PA194CodeInstance.unary_of_three sourcePath (pair tag payload+1) choices
  have hdef : 𝚺₁-Predicate (fun k : M => F sourcePath ![k,pair tag payload+1,choices] = pair tag payload+1) := by definability
  induction n using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => exact sourcePath_zero _ _
  case succ n ih =>
    rw [sourcePath_succ,ih,sourceChild_leaf tag payload _ ht]

theorem internalQuantifierFree_leaf (tag payload : M)
    (ht : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3) :
    InternalQuantifierFree (pair tag payload+1) := by
  intro ⟨a,ha⟩
  rcases ha with ha | ha
  · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ ha
    rw [sourcePath_leaf_stationary tag payload choices steps ht] at hpath
    have ht' := congrArg (fun p : M => F nodeTag ![p]) hpath
    change F nodeTag ![pair tag payload+1] = F nodeTag ![pair (6 : M) a+1] at ht'
    rw [nodeTag_model,nodeTag_model] at ht'
    rcases ht with rfl | rfl | rfl | rfl <;> norm_num at ht'
  · obtain ⟨depth,steps,choices,hpath,_⟩ := codedSyntacticDescendant_coverage _ _ ha
    rw [sourcePath_leaf_stationary tag payload choices steps ht] at hpath
    have ht' := congrArg (fun p : M => F nodeTag ![p]) hpath
    change F nodeTag ![pair tag payload+1] = F nodeTag ![pair (7 : M) a+1] at ht'
    rw [nodeTag_model,nodeTag_model] at ht'
    rcases ht with rfl | rfl | rfl | rfl <;> norm_num at ht'

/-- Quantifier-free syntax has numerically identical translations at consecutive
binder bases, including nonstandard formula codes. -/
theorem quantifierFree_baseShift (p bound free base reserve : M)
    (hp : IsUFormula SourceL p) (hqf : InternalQuantifierFree p) :
    F fixedFormulaTranslation ![p,bound,free,base,reserve] =
      F fixedFormulaTranslation ![p,bound,free,base+1,reserve] := by
  let e := pair bound (pair free (pair base reserve))
  let e' := pair bound (pair free (pair (base+1) reserve))
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚷₁-Predicate (InternalQuantifierFree : M → Prop) := internalQuantifierFree_definable
  have hdef : 𝚺₁-Predicate (fun q : M => InternalQuantifierFree q →
      positiveTranslation e q = positiveTranslation e' q) := by definability
  have hall : ∀ q, IsUFormula SourceL q → InternalQuantifierFree q →
      positiveTranslation e q = positiveTranslation e' q := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv _
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model]
      exact positiveAtom_base_irrelevant r v bound free base (base+1) reserve hr hv
    · intro arity r v hr hv _
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model,
        fixedFormulaTranslation_atom_polarity r v bound free base reserve hr hv,
        fixedFormulaTranslation_atom_polarity r v bound free (base+1) reserve hr hv,
        positiveAtom_base_irrelevant r v bound free base (base+1) reserve hr hv]
    · intro _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
    · intro _
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
    · intro a b ha hb iha ihb hfree
      have hleft : SourceDirectEdge (a ^⋏ b) a 0 := by
        left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋏ b) b 0 := by
        left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      have ih1 := iha (internalQuantifierFree_child _ _ _ hleft hfree)
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hright hfree)
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_and a b _ _ _ _ ha hb,
        fixedFormulaTranslation_and a b _ _ _ _ ha hb,ih1,ih2]
    · intro a b ha hb iha ihb hfree
      have hleft : SourceDirectEdge (a ^⋎ b) a 0 := by
        right; left; exact ⟨a,b,rfl,Or.inl rfl,rfl⟩
      have hright : SourceDirectEdge (a ^⋎ b) b 0 := by
        right; left; exact ⟨a,b,rfl,Or.inr rfl,rfl⟩
      have ih1 := iha (internalQuantifierFree_child _ _ _ hleft hfree)
      have ih2 := ihb (internalQuantifierFree_child _ _ _ hright hfree)
      dsimp only [e,e'] at ih1 ih2 ⊢
      rw [positiveTranslation_model,positiveTranslation_model] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_or a b _ _ _ _ ha hb,
        fixedFormulaTranslation_or a b _ _ _ _ ha hb,ih1,ih2]
    · intro a ha ih hfree
      exact False.elim (internalQuantifierFree_not_all a hfree)
    · intro a ha ih hfree
      exact False.elim (internalQuantifierFree_not_ex a hfree)
  have hh := hall p hp hqf
  dsimp only [e,e'] at hh
  simpa only [positiveTranslation_model] using hh

/-- The exact eigenlabel-vacuity field for every quantifier-free source
sequent formula, under the concrete ranked/empty-bound admission. -/
theorem simRuleAllFresh_quantifierFree (e s q d : M)
    (hs : IsFormulaSet SourceL s) (hq : q ∈ s) (ha : RankedAdmission e d) (hb : simBound e = 0)
    (hqf : InternalQuantifierFree q) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q)
      (numericalQuant.all (simBase e) (numericalTranslation.tr e q))) := by
  have he := quantifierFree_baseShift q (simBound e) (simFree e) (simBase e) (simReserve e)
    (hs _ hq).isUFormula hqf
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  · rw [he]; exact imp_refl _
  · rw [he]; exact imp_refl _

#print axioms internalQuantifierFree_definable
#print axioms internalQuantifierFree_child
#print axioms sourcePath_leaf_stationary
#print axioms internalQuantifierFree_leaf
#print axioms quantifierFree_baseShift
#print axioms simRuleAllFresh_quantifierFree
end models
end PA194ModelLogic
