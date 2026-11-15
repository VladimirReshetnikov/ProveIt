import PA194ModelSourceSubstGeneral
import PA194ModelObsGeneral
import PA194ModelBaseFreshGeneral
import PA194ModelFullQF
import PA194ModelSafeQF
import PA194ModelExMembership
import PA194ModelSeedEnvironment
import PA194ModelDescendantComplexity
import PA194ModelRankedEnvironment
import PA194ModelDualInduction
import PA194ModelAtomicFreshness
import PA194RelExtTypedTranslation

/-! General target witness and seeded existential-introduction rule. -/
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
local instance existGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance existGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance existGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance existGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance existGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance existGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- General existential witness introduction with arbitrary internal syntax. -/
theorem targetExists_general_freeWitness (p x c free reserve : M)
    (hp : IsSemiformula SourceL 1 p)
    (hcx : c < x) (hfree : ∀ i : M, free.[i] < x)
    (hbudget : x+p+2 < reserve) :
    TargetProvable (impValue
      (F fixedFormulaTranslation ![p,pair c (0 : M)+1,free,x,reserve])
      (exValue x (F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve]))) := by
  have hxpos : (0 : M) < x := lt_of_le_of_lt zero_le hcx
  have hxres : x < reserve := lt_of_le_of_lt
    (show x ≤ x+p+2 from le_trans le_self_add le_self_add) hbudget
  have hcres : c < reserve := lt_trans hcx hxres
  have hres0 : (0 : M) < reserve := lt_trans hxpos hxres
  have hin0 : ∀ i ≤ p, ((0 : M)).[i] < x := by intro i _; simpa using hxpos
  have hin : ∀ i ≤ p, (pair c (0 : M)+1).[i] < x := pushLabels_below c 0 p x hcx hin0
  have hf : ∀ i ≤ p, free.[i] < x := by intro i _; exact hfree i
  have hnorm := generalBaseShift_all_codes p (pair c (0 : M)+1) free x reserve hp.isUFormula hin hf hbudget
  have hbase : (x+1)+p < reserve := by
    have hh : (x+1)+p ≤ x+p+2 := by
      have hz : (0 : M) ≤ 1 := zero_le
      have hz' := add_le_add_right hz (x+p+1)
      simpa only [add_assoc,add_comm,add_left_comm,zero_add,one_add_one_eq_two] using hz'
    exact lt_of_le_of_lt hh hbudget
  have hinit0 : ∀ i ≤ p, ((0 : M)).[i] < reserve := by intro i _; simpa using hres0
  have hinit₁ : ∀ i ≤ p, (pair x (0 : M)+1).[i] < reserve := pushLabels_below x 0 p reserve hxres hinit0
  have hinit₂ : ∀ i ≤ p, (pair c (0 : M)+1).[i] < reserve := pushLabels_below c 0 p reserve hcres hinit0
  have hfree' : ∀ i ≤ p, free.[i] < reserve := by intro i _; exact lt_trans (hfree i) hxres
  have hobs := observationalRewrite_all_codes x c p (pair x (0 : M)+1) (pair c (0 : M)+1)
    free (x+1) reserve hp.isUFormula (lt_add_one x) (lt_trans hcx (lt_add_one x)) hbase
    (pushLabels_aligned x c 0 p) hinit₁ hinit₂ hfree'
  let P := F fixedFormulaTranslation ![p,pair x (0 : M)+1,free,x+1,reserve]
  let Q := F fixedFormulaTranslation ![p,pair c (0 : M)+1,free,x+1,reserve]
  let Q0 := F fixedFormulaTranslation ![p,pair c (0 : M)+1,free,x,reserve]
  let E := eqValue c x
  let N := neighborhoodValue c x reserve
  have hn : TargetProvable (impValue E N) :=
    primitiveToNeighborhood_target c x reserve (ne_of_gt hcres) (ne_of_gt hxres)
  have hrew : TargetPremiseRewrite E P Q := by
    constructor
    · let he : Ctx [P,E] E := .assumption (by simp)
      let hp' : Ctx [P,E] P := .assumption (by simp)
      let hn' : Ctx [P,E] N := .mp he (.closed hn)
      exact (Ctx.mp hp' (.mp hn' (.closed hobs.1))).deduction.deduction.empty
    · let he : Ctx [Q,E] E := .assumption (by simp)
      let hq : Ctx [Q,E] Q := .assumption (by simp)
      let hn' : Ctx [Q,E] N := .mp he (.closed hn)
      exact (Ctx.mp hq (.mp hn' (.closed hobs.2))).deduction.deduction.empty
  let A := negValue P
  let B := negValue Q
  have hx0 : (0 : M) ≠ x := ne_of_lt hxpos
  have hcne : c ≠ x := ne_of_lt hcx
  have hbound : ∀ i ≤ p, (pair c (0 : M)+1).[i] ≠ x := by
    intro i _; exact singletonStack_avoids c x hcne hx0 i
  have hfx : ∀ i ≤ p, free.[i] ≠ x := by intro i _; exact ne_of_lt (hfree i)
  have hv := generalVacuity_below_all_codes x p (pair c (0 : M)+1) free (x+1) reserve
    hp.isUFormula (lt_add_one x) hbound hfx (ne_of_lt hxres)
  unfold GeneralVacuity at hv
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hv
  have hvB : TargetProvable (impValue B (allValue x B)) := negationVacuity x Q hv
  have hneg := targetPremiseRewrite_neg E P Q hrew
  have hs : TargetProvable (impValue (allValue x A) B) :=
    specializeWithMirroredEquality_target x c A B hvB hneg.1
  have hqexists : TargetProvable (impValue Q (exValue x P)) := by
    let hq : Ctx [allValue x A,Q] Q := .assumption (by simp)
    let hall : Ctx [allValue x A,Q] (allValue x A) := .assumption (by simp)
    let hn' : Ctx [allValue x A,Q] B := .mp hall (.closed hs)
    exact (Ctx.mp hq hn').deduction.deduction.empty
  let hq0 : Ctx [Q0] Q0 := .assumption (by simp)
  let hq : Ctx [Q0] Q := .mp hq0 (.closed hnorm.1)
  exact (Ctx.mp hq (.closed hqexists)).deduction.empty

theorem exsIntro_generalBaseSlack (e s p t d : M)
    (hm : (^∃ p) ∈ s) (ha : RankedAdmission e (exsIntro s p t d)) :
    simBase e+p+2 < simReserve e := by
  have hpc : p < ^∃ p := by
    change p < pair (7 : M) p+1
    exact lt_of_le_of_lt (le_pair_right (7 : M) p) (lt_add_one _)
  have hps : p < s := lt_trans hpc (lt_of_mem hm)
  have hse : s < exsIntro s p t d := seq_lt_exsIntro s p t d
  have hp1 : p+1 ≤ s := lt_iff_succ_le.mp hps
  have hs1 : s+1 ≤ exsIntro s p t d := lt_iff_succ_le.mp hse
  have hp2 : p+2 ≤ exsIntro s p t d := by
    have hh := add_le_add_right hp1 1
    have he : p+2 = (p+1)+1 := by norm_num [add_assoc]
    rw [he]
    exact le_trans (by simpa only [add_comm] using hh) hs1
  have hl : p+2 < exsIntro s p t d+1 := lt_of_le_of_lt hp2 (lt_add_one _)
  have hh := add_lt_add_right hl (simBase e)
  have hl' : simBase e+p+2 < simBase e+(exsIntro s p t d+1) := by
    simpa only [add_assoc,add_comm,add_left_comm] using hh
  exact lt_of_lt_of_le hl' ha.2

/-- Full existential-introduction field under the seeded admission invariant. -/
theorem simRuleExs_generalSeed (reserve e s p t d : M)
    (ha : SeedAdmission 0 reserve e (exsIntro s p t d))
    (hs : IsFormulaSet SourceL s) (hm : (^∃ p) ∈ s) (ht : IsTerm SourceL t) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t p)) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ p)) 1)) := by
  obtain ⟨j,rfl⟩ := sourceClosedTerm_is_fvar t ht
  have hbody : IsSemiformula SourceL 1 p := by
    have hf := hs _ hm
    simpa only [IsSemiformula.exs,zero_add] using hf
  have hrank : RankedAdmission e (exsIntro s p (^&j) d) := depthAdmission_ranked e _ ha.1
  have hb : simBound e = 0 := ha.2.2.1
  have hcx : (simFree e).[j] < simBase e := rankedEnvironment_free_lt e j hrank.1
  have hfree : ∀ i : M, (simFree e).[i] < simBase e := fun i => rankedEnvironment_free_lt e i hrank.1
  apply simRuleExs_of_intro e s p (^&j) hs hm (by simp)
  rw [fixedFormulaTranslation_ex _ _ _ _ _ hbody.isUFormula]
  rw [sourceSubst_translation p (simBound e) (simFree e) (simBase e) j (simReserve e) hbody,hb]
  exact targetExists_general_freeWitness p (simBase e) (simFree e).[j] (simFree e) (simReserve e)
    hbody hcx hfree (exsIntro_generalBaseSlack e s p (^&j) d hm hrank)

#print axioms exsIntro_generalBaseSlack
#print axioms simRuleExs_generalSeed
#print axioms targetExists_general_freeWitness
end models
end PA194ModelLogic
