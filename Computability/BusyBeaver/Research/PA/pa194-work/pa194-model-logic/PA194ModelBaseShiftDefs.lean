import PA194ModelCrossBinder
import PA194ModelSafeQF
import PA194ModelExMembership
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
local instance baseShiftDefZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance baseShiftDefOne : One M := ⟨F oneCode Fin.elim0⟩
local instance baseShiftDefAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance baseShiftDefMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance baseShiftDefLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance baseShiftDefIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






def TargetEquiv (A B : M) : Prop :=
  TargetProvable (impValue A B) ∧ TargetProvable (impValue B A)

theorem targetEquiv_refl (A : M) : TargetEquiv A A := ⟨imp_refl A,imp_refl A⟩

theorem targetEquiv_addPremise (E A B : M) (h : TargetEquiv A B) : TargetPremiseRewrite E A B :=
  ⟨tp_mp h.1 (imp_k (impValue A B) E),tp_mp h.2 (imp_k (impValue B A) E)⟩

theorem targetPremiseRewrite_removeTruth (A B : M) (h : TargetPremiseRewrite 0 A B) : TargetEquiv A B :=
  ⟨tp_mp sequentTruth_zero h.1,tp_mp sequentTruth_zero h.2⟩

theorem targetEquiv_and (A B C D : M) (h₁ : TargetEquiv A B) (h₂ : TargetEquiv C D) :
    TargetEquiv (conjValue A C) (conjValue B D) :=
  targetPremiseRewrite_removeTruth _ _ (targetPremiseRewrite_and 0 _ _ _ _
    (targetEquiv_addPremise 0 _ _ h₁) (targetEquiv_addPremise 0 _ _ h₂))

theorem targetEquiv_or (A B C D : M) (h₁ : TargetEquiv A B) (h₂ : TargetEquiv C D) :
    TargetEquiv (impValue (negValue A) C) (impValue (negValue B) D) :=
  targetPremiseRewrite_removeTruth _ _ (targetPremiseRewrite_imp 0 _ _ _ _
    (targetPremiseRewrite_neg 0 _ _ (targetEquiv_addPremise 0 _ _ h₁)) (targetEquiv_addPremise 0 _ _ h₂))

noncomputable def shiftedDepthEnvironment (initial free base reserve k : M) : M :=
  pair (F allocateBound ![k,base,initial]) (pair free (pair (base+k+1) reserve))

noncomputable def depthBaseShift (initial free base reserve p k : M) : Prop :=
  TargetEquiv
    (positiveTranslation (depthEnvironment initial free base reserve k) p)
    (positiveTranslation (shiftedDepthEnvironment initial free base reserve k) p)

theorem depthBaseShift_definable (initial free base reserve : M) :
    𝚺₁-Relation (depthBaseShift initial free base reserve) := by
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₂ (impValue : M → M → M) := (numericalCalc (M := M)).imp_defined.to_definable
  haveI : 𝚺₁-Predicate (TargetProvable : M → Prop) := targetProvable_definable
  haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base,initial]) :=
    PA194CodeInstance.unary_of_three allocateBound base initial
  haveI : 𝚺₁-Function₁ (depthEnvironment initial free base reserve) := by
    unfold depthEnvironment; definability
  haveI : 𝚺₁-Function₁ (shiftedDepthEnvironment initial free base reserve) := by
    unfold shiftedDepthEnvironment; definability
  haveI : 𝚺₁-Function₂ (fun p k : M => positiveTranslation (depthEnvironment initial free base reserve k) p) := by
    definability
  haveI : 𝚺₁-Function₂ (fun p k : M => positiveTranslation
      (shiftedDepthEnvironment initial free base reserve k) p) := by
    definability
  unfold depthBaseShift TargetEquiv
  definability

theorem depthBaseShift_eq (initial free base reserve p k : M) :
    depthBaseShift initial free base reserve p k ↔
      TargetEquiv
        (F fixedFormulaTranslation ![p,F allocateBound ![k,base,initial],free,base+k,reserve])
        (F fixedFormulaTranslation ![p,F allocateBound ![k,base,initial],free,base+k+1,reserve]) := by
  unfold depthBaseShift depthEnvironment shiftedDepthEnvironment
  rw [positiveTranslation_model,positiveTranslation_model]

#print axioms targetEquiv_and
#print axioms targetEquiv_or
#print axioms depthBaseShift_definable
#print axioms depthBaseShift_eq
end models
end PA194ModelLogic
