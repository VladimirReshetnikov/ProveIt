import PA194ModelAtomicAlpha
import PA194ModelBelowFreshInduction
import PA194ModelQuantifierFreeFresh
import PA194ModelSeedEnvironment
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
local instance twoAlphaZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance twoAlphaOne : One M := ⟨F oneCode Fin.elim0⟩
local instance twoAlphaAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance twoAlphaMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance twoAlphaLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance twoAlphaIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]








/-- Alpha-convert two nested universal binders using a third distinct label. -/
theorem targetTwoAllMembershipAlpha (x y z : M) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    TargetProvable (impValue (allValue x (allValue y (memValue y x)))
      (allValue y (allValue z (memValue z y)))) := by
  have h1 := liftImp x (targetMembershipAllAlphaLeft y z x hyz (Ne.symm hxy) (Ne.symm hxz))
  have h2 := r4 x z (memValue z x)
  have h3 := liftImp z (targetMembershipAllAlphaRight x y z hxy hxz hyz)
  have h4 := r4 z y (memValue z y)
  exact imp_trans h1 (imp_trans h2 (imp_trans h3 h4))

theorem targetTwoAllMembershipAlpha_reverse (x y z : M) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    TargetProvable (impValue (allValue y (allValue z (memValue z y)))
      (allValue x (allValue y (memValue y x)))) := by
  have h1 := r4 y z (memValue z y)
  have h2 := liftImp z (targetMembershipAllAlphaRight y x z (Ne.symm hxy) hyz hxz)
  have h3 := r4 z x (memValue z x)
  have h4 := liftImp x (targetMembershipAllAlphaLeft z y x (Ne.symm hyz) (Ne.symm hxz) (Ne.symm hxy))
  exact imp_trans h1 (imp_trans h2 (imp_trans h3 h4))

theorem fixedTranslation_twoAllMembership (bound free base reserve : M) :
    F fixedFormulaTranslation ![^∀ (^∀ (^rel (2 : M) (1 : M) ?[^#(1 : M),^#(0 : M)])),
      bound,free,base,reserve] =
      allValue base (allValue (base+1) (memValue (base+1) base)) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv : IsUTermVec SourceL 2 (?[ ^#(1 : M),^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^rel (2 : M) (1 : M) ?[^#(1 : M),^#(0 : M)]) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  have hpall : IsUFormula SourceL (^∀ (^rel (2 : M) (1 : M) ?[^#(1 : M),^#(0 : M)])) := by
    simpa only [IsUFormula.all] using hp
  rw [fixedFormulaTranslation_all _ _ _ _ _ hpall,fixedFormulaTranslation_all _ _ _ _ _ hp,
    fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [Arithmetic.one_ne_zero,ite_false,adjoin_def]
  rw [membershipAtom_model,termLabel_bound_nth,termLabel_bound_nth]
  simp [←adjoin_def]

theorem simRuleAllFresh_twoAllMembership (e s d : M)
    (hs : IsFormulaSet SourceL s)
    (hq : (^∀ (^∀ (^rel (2 : M) (1 : M) ?[^#(1 : M),^#(0 : M)]))) ∈ s)
    (ha : RankedAdmission e d) (hb : simBound e = 0) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^∀ (^rel (2 : M) (1 : M) ?[^#(1 : M),^#(0 : M)]))))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^∀ (^rel (2 : M) (1 : M) ?[^#(1 : M),^#(0 : M)])))))) := by
  let q : M := ^∀ (^∀ (^rel (2 : M) (1 : M) ?[^#(1 : M),^#(0 : M)]))
  apply simRuleAllFresh_of_baseShift e s q d hs hq ha hb
  all_goals
    change TargetProvable (impValue
      (F fixedFormulaTranslation ![^∀ (^∀ (^rel (2 : M) (1 : M) ?[^#(1 : M),^#(0 : M)])),_,_,_,_])
      (F fixedFormulaTranslation ![^∀ (^∀ (^rel (2 : M) (1 : M) ?[^#(1 : M),^#(0 : M)])),_,_,_,_]))
    rw [fixedTranslation_twoAllMembership,fixedTranslation_twoAllMembership]
    have hxy : simBase e ≠ simBase e+1 := ne_of_lt (lt_add_one _)
    have hyz : simBase e+1 ≠ (simBase e+1)+1 := ne_of_lt (lt_add_one _)
    have hxz : simBase e ≠ (simBase e+1)+1 := ne_of_lt (lt_trans (lt_add_one _) (lt_add_one _))
  · exact targetTwoAllMembershipAlpha _ _ _ hxy hxz hyz
  · exact targetTwoAllMembershipAlpha_reverse _ _ _ hxy hxz hyz

#print axioms targetTwoAllMembershipAlpha
#print axioms targetTwoAllMembershipAlpha_reverse
#print axioms fixedTranslation_twoAllMembership
#print axioms simRuleAllFresh_twoAllMembership
end models
end PA194ModelLogic
