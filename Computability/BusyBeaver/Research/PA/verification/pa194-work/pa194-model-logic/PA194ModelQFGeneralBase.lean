import PA194ModelQuantifierFreeFresh
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
local instance qfGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance qfGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance qfGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance qfGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance qfGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance qfGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]





theorem quantifierFree_anyBases (p bound free base₁ base₂ reserve : M)
    (hp : IsUFormula SourceL p) (hqf : InternalQuantifierFree p) :
    F fixedFormulaTranslation ![p,bound,free,base₁,reserve] =
      F fixedFormulaTranslation ![p,bound,free,base₂,reserve] := by
  let e := pair bound (pair free (pair base₁ reserve))
  let e' := pair bound (pair free (pair (base₂) reserve))
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
      exact positiveAtom_base_irrelevant r v bound free base₁ (base₂) reserve hr hv
    · intro arity r v hr hv _
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      dsimp only [e,e']
      rw [positiveTranslation_model,positiveTranslation_model,
        fixedFormulaTranslation_atom_polarity r v bound free base₁ reserve hr hv,
        fixedFormulaTranslation_atom_polarity r v bound free (base₂) reserve hr hv,
        positiveAtom_base_irrelevant r v bound free base₁ (base₂) reserve hr hv]
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


#print axioms quantifierFree_anyBases
end models
end PA194ModelLogic
