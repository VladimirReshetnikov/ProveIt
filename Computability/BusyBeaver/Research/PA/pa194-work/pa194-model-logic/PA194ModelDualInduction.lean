import PA194ModelDualQuantifier
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
local instance dualInductionZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance dualInductionOne : One M := ⟨F oneCode Fin.elim0⟩
local instance dualInductionAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance dualInductionMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance dualInductionLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance dualInductionIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def sequentPositiveCode : Code 2 :=
  .comp fixedFormulaTranslation
    (.cons (.proj 1) (.cons sequentEnvBound (.cons sequentEnvFree
      (.cons sequentEnvBase (.cons sequentEnvReserve (.nil 2))))))
noncomputable def positiveTranslation (e p : M) : M := F sequentPositiveCode ![e,p]

noncomputable def positiveTr : ConPA.Sequent.Tr M where
  tr := positiveTranslation
  trDef := PA194CodeGraph.graph sequentPositiveCode
  tr_defined := .mk fun v => by
    have h := (PA194CodeGraph.modelGraph (M := M) sequentPositiveCode).defined v
    have hv : (fun i : Fin 2 => v i.succ) = ![v 1,v 2] := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun k => Fin.elim0 k) j
    rw [hv] at h
    dsimp only at h
    simpa [positiveTranslation] using h

theorem positiveTranslation_model (bound free base reserve p : M) :
    positiveTranslation (pair bound (pair free (pair base reserve))) p =
      F fixedFormulaTranslation ![p,bound,free,base,reserve] := by
  simp only [positiveTranslation,sequentPositiveCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change F (.proj 1 : Code 2) ![pair bound (pair free (pair base reserve)),p] = p
    simp [modelProjection]
  refine Fin.cases ?_ (fun k => ?_) j
  · change F sequentEnvBound ![pair bound (pair free (pair base reserve)),p] = bound
    simp [sequentEnvBound,modelUnary,modelProjection,
      modelPi1Code firstProjection firstProjection_certified,pi₁_pair]
  refine Fin.cases ?_ (fun l => ?_) k
  · change F sequentEnvFree ![pair bound (pair free (pair base reserve)),p] = free
    simp [sequentEnvFree,sequentEnvTail,modelUnary,modelProjection,
      modelPi1Code firstProjection firstProjection_certified,
      modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair]
  refine Fin.cases ?_ (fun m => ?_) l
  · change F sequentEnvBase ![pair bound (pair free (pair base reserve)),p] = base
    simp [sequentEnvBase,sequentEnvLabels,sequentEnvTail,modelUnary,modelProjection,
      modelPi1Code firstProjection firstProjection_certified,
      modelPi2Code secondProjection secondProjection_certified,pi₁_pair,pi₂_pair]
  refine Fin.cases ?_ (fun n => Fin.elim0 n) m
  · change F sequentEnvReserve ![pair bound (pair free (pair base reserve)),p] = reserve
    simp [sequentEnvReserve,sequentEnvLabels,sequentEnvTail,modelUnary,modelProjection,
      modelPi2Code secondProjection secondProjection_certified,pi₂_pair]

noncomputable def depthEnvironment (initial free base reserve k : M) : M :=
  pair (F allocateBound ![k,base,initial]) (pair free (pair (base+k) reserve))

noncomputable def depthDual (initial free base reserve p k : M) : Prop :=
  let e := depthEnvironment initial free base reserve k
  TargetDual (positiveTranslation e p)
    (positiveTranslation e (neg M6.PA.RelationalSource.language p))

theorem depthDual_definable (initial free base reserve : M) :
    𝚺₁-Relation (depthDual initial free base reserve) := by
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base,initial]) :=
    PA194CodeInstance.unary_of_three allocateBound base initial
  haveI : 𝚺₁-Function₂ (impValue : M → M → M) := (numericalCalc (M := M)).imp_defined.to_definable
  haveI : 𝚺₁-Predicate (TargetProvable : M → Prop) := targetProvable_definable
  haveI : 𝚺₁-Function₁ (negValue : M → M) := by unfold negValue; definability
  haveI : 𝚺₁-Function₁ (depthEnvironment initial free base reserve) := by
    unfold depthEnvironment
    definability
  haveI : 𝚺₁-Function₂ (fun p k : M => positiveTranslation (depthEnvironment initial free base reserve k) p) := by
    definability
  haveI : 𝚺₁-Function₂ (fun p k : M => positiveTranslation (depthEnvironment initial free base reserve k)
      (neg M6.PA.RelationalSource.language p)) := by definability
  unfold depthDual TargetDual
  definability

theorem depthDual_eq (initial free base reserve p k : M) :
    depthDual initial free base reserve p k ↔
      TranslationDual p (F allocateBound ![k,base,initial]) free (base+k) reserve := by
  unfold depthDual depthEnvironment TranslationDual
  dsimp only
  rw [positiveTranslation_model,positiveTranslation_model]

/-- Full target-provable source-negation duality for every internally valid
source formula, including nonstandard codes, at arbitrary environments. -/
theorem translationDual_all_codes (p initial free base reserve : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    TranslationDual p initial free base reserve := by
  let K := p
  haveI : 𝚺₁-Relation (depthDual initial free base reserve) := depthDual_definable initial free base reserve
  have hdef : 𝚺₁-Predicate (fun x : M => ∀ k ≤ K, x+k ≤ K → depthDual initial free base reserve x k) := by
    definability
  have hall : ∀ x, IsUFormula M6.PA.RelationalSource.language x →
      ∀ k ≤ K, x+k ≤ K → depthDual initial free base reserve x k := by
    intro x hx
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ x hx
    · intro arity r v hr hv k hk hbound
      have ha := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      rw [depthDual_eq]
      exact translationDual_positiveAtom r v _ _ _ _ hr hv
    · intro arity r v hr hv k hk hbound
      have ha := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      rw [depthDual_eq]
      exact translationDual_negativeAtom r v _ _ _ _ hr hv
    · intro k hk hbound
      rw [depthDual_eq]
      exact translationDual_verum _ _ _ _
    · intro k hk hbound
      rw [depthDual_eq]
      exact translationDual_falsum _ _ _ _
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA
      have ih2 := ihb k hk hB
      rw [depthDual_eq] at ih1 ih2 ⊢
      exact translationDual_and a b _ _ _ _ ha hb ih1 ih2
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA
      have ih2 := ihb k hk hB
      rw [depthDual_eq] at ih1 ih2 ⊢
      exact translationDual_or a b _ _ _ _ ha hb ih1 ih2
    · intro a ha ih k hk hbound
      have hle : a+1 ≤ ^∀ a := by
        change a+1 ≤ pair (6 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have ih1 := ih (k+1) hk1 hA
      rw [depthDual_eq] at ih1 ⊢
      apply translationDual_all a _ _ _ _ ha
      simpa only [allocateBound_succ,add_assoc] using ih1
    · intro a ha ih k hk hbound
      have hle : a+1 ≤ ^∃ a := by
        change a+1 ≤ pair (7 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (7 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have ih1 := ih (k+1) hk1 hA
      rw [depthDual_eq] at ih1 ⊢
      apply translationDual_ex a _ _ _ _ ha
      simpa only [allocateBound_succ,add_assoc] using ih1
  have h0 := hall p hp 0 (show (0 : M) ≤ K from zero_le) (by simp [K])
  rw [depthDual_eq] at h0
  simpa only [allocateBound_zero,add_zero] using h0

#print axioms depthDual_eq
#print axioms translationDual_all_codes
#print axioms positiveTranslation_model
#print axioms depthDual_definable
end models
end PA194ModelLogic
