import PA194ModelSourceOpeningAtom
import PA194ModelDepthRules
import PA194ModelQuantifierFreeFresh
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
local instance sourceOpeningGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceOpeningGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceOpeningGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceOpeningGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceOpeningGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceOpeningGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem sourceOpeningFormula_valid (limit s k p : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (hp : IsSemiformula SourceL (k+1) p) :
    IsSemiformula SourceL k (sourceOpeningFormula s k p) := by
  exact hp.shift.subst (sourceQVec_trace_typed limit s h hl k hk)

theorem sourceOpeningFormula_and (s k a b : M) (ha : IsUFormula SourceL a) (hb : IsUFormula SourceL b) :
    sourceOpeningFormula s k (a ^⋏ b) = sourceOpeningFormula s k a ^⋏ sourceOpeningFormula s k b := by
  simp only [sourceOpeningFormula,shift_and ha hb,substs_and ha.shift hb.shift]

theorem sourceOpeningFormula_or (s k a b : M) (ha : IsUFormula SourceL a) (hb : IsUFormula SourceL b) :
    sourceOpeningFormula s k (a ^⋎ b) = sourceOpeningFormula s k a ^⋎ sourceOpeningFormula s k b := by
  simp only [sourceOpeningFormula,shift_or ha hb,substs_or ha.shift hb.shift]

theorem sourceOpeningFormula_all (limit s k a : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k < limit) (ha : IsUFormula SourceL a) :
    sourceOpeningFormula s k (^∀ a) = ^∀ (sourceOpeningFormula s (k+1) a) := by
  rw [sourceOpeningFormula,shift_all ha,substs_all ha.shift,
    ← sourceQVec_trace_step _ limit s k h hl hk]
  rfl

theorem sourceOpeningFormula_ex (limit s k a : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&(0 : M)] : M)] s)
    (hl : limit + 1 = lh s) (hk : k < limit) (ha : IsUFormula SourceL a) :
    sourceOpeningFormula s k (^∃ a) = ^∃ (sourceOpeningFormula s (k+1) a) := by
  rw [sourceOpeningFormula,shift_exs ha,substs_ex ha.shift,
    ← sourceQVec_trace_step _ limit s k h hl hk]
  rfl

noncomputable def depthSourceOpening (s bound free base reserve p k : M) : Prop :=
  positiveTranslation (depthEnvironment bound (pair base free+1) (base+1) reserve k) (sourceOpeningFormula s k p) =
    positiveTranslation (depthEnvironment (pair base bound+1) free (base+1) reserve k) p

theorem depthSourceOpening_definable (s bound free base reserve : M) :
    𝚺₁-Relation (depthSourceOpening s bound free base reserve) := by
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₂ (fun (p k : M) => sourceOpeningFormula s k p) := by
    unfold sourceOpeningFormula
    definability
  haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base+1,bound]) :=
    PA194CodeInstance.unary_of_three allocateBound (base+1) bound
  haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base+1,pair base bound+1]) :=
    PA194CodeInstance.unary_of_three allocateBound (base+1) (pair base bound+1)
  haveI : 𝚺₁-Function₁ (depthEnvironment bound (pair base free+1) (base+1) reserve) := by
    unfold depthEnvironment; definability
  haveI : 𝚺₁-Function₁ (depthEnvironment (pair base bound+1) free (base+1) reserve) := by
    unfold depthEnvironment; definability
  unfold depthSourceOpening
  definability

theorem depthSourceOpening_eq (s bound free base reserve p k : M) :
    depthSourceOpening s bound free base reserve p k ↔
      F fixedFormulaTranslation ![sourceOpeningFormula s k p,F allocateBound ![k,base+1,bound],
        pair base free+1,base+1+k,reserve] =
      F fixedFormulaTranslation ![p,F allocateBound ![k,base+1,pair base bound+1],free,base+1+k,reserve] := by
  unfold depthSourceOpening depthEnvironment
  rw [positiveTranslation_model,positiveTranslation_model]

/-- Exact source opening through arbitrary nonstandard quantifier depth. -/
theorem sourceOpening_freeBridge (p bound free base reserve : M)
    (hp : IsSemiformula SourceL 1 p) : FreeBridge p bound free base reserve := by
  let K := p
  obtain ⟨s,hs,hl⟩ := sourceQVec_exists_trace (?[ ^&(0 : M)] : M) K
  haveI : 𝚺₁-Relation (depthSourceOpening s bound free base reserve) :=
    depthSourceOpening_definable s bound free base reserve
  have hdef : 𝚺₁-Predicate (fun q : M => ∀ k ≤ K, q+k ≤ K → IsSemiformula SourceL (k+1) q →
      depthSourceOpening s bound free base reserve q k) := by definability
  have hall : ∀ q, IsUFormula SourceL q → ∀ k ≤ K, q+k ≤ K → IsSemiformula SourceL (k+1) q →
      depthSourceOpening s bound free base reserve q k := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv k hk hbound hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
      rw [depthSourceOpening_eq]
      exact sourceOpening_positiveAtom K s k r a b bound free base reserve hs hl hk hr hsa hsb
    · intro arity r v hr hv k hk hbound hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
      rw [depthSourceOpening_eq]
      exact sourceOpening_negativeAtom K s k r a b bound free base reserve hs hl hk hr hsa hsb
    · intro k hk hbound hscope
      rw [depthSourceOpening_eq]
      simp only [sourceOpeningFormula,shift_verum,substs_verum]
      rw [fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
    · intro k hk hbound hscope
      rw [depthSourceOpening_eq]
      simp only [sourceOpeningFormula,shift_falsum,substs_falsum]
      rw [fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
    · intro a b ha hb iha ihb k hk hbound hscope
      have hleA : a ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      obtain ⟨hsa,hsb⟩ := IsSemiformula.and.mp hscope
      have ih1 := iha k hk hA hsa
      have ih2 := ihb k hk hB hsb
      rw [depthSourceOpening_eq] at ih1 ih2 ⊢
      rw [sourceOpeningFormula_and s k a b ha hb,
        fixedFormulaTranslation_and _ _ _ _ _ _ (sourceOpeningFormula_valid K s k a hs hl hk hsa).isUFormula (sourceOpeningFormula_valid K s k b hs hl hk hsb).isUFormula,
        fixedFormulaTranslation_and _ _ _ _ _ _ ha hb,ih1,ih2]
    · intro a b ha hb iha ihb k hk hbound hscope
      have hleA : a ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      obtain ⟨hsa,hsb⟩ := IsSemiformula.or.mp hscope
      have ih1 := iha k hk hA hsa
      have ih2 := ihb k hk hB hsb
      rw [depthSourceOpening_eq] at ih1 ih2 ⊢
      rw [sourceOpeningFormula_or s k a b ha hb,
        fixedFormulaTranslation_or _ _ _ _ _ _ (sourceOpeningFormula_valid K s k a hs hl hk hsa).isUFormula (sourceOpeningFormula_valid K s k b hs hl hk hsb).isUFormula,
        fixedFormulaTranslation_or _ _ _ _ _ _ ha hb,ih1,ih2]
    · intro a ha ih k hk hbound hscope
      have hle : a+1 ≤ ^∀ a := by
        change a+1 ≤ pair (6 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (6 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have hka : k < K := lt_iff_succ_le.mpr hk1
      have hsa : IsSemiformula SourceL ((k+1)+1) a := by simpa only [IsSemiformula.all] using hscope
      have ih1 := ih (k+1) hk1 hA hsa
      rw [depthSourceOpening_eq] at ih1 ⊢
      rw [sourceOpeningFormula_all K s k a hs hl hka ha,
        fixedFormulaTranslation_all _ _ _ _ _ (sourceOpeningFormula_valid K s (k+1) a hs hl hk1 hsa).isUFormula,
        fixedFormulaTranslation_all _ _ _ _ _ ha]
      rw [allocateBound_succ,allocateBound_succ] at ih1
      have hbaseEq : base+1+(k+1) = (base+1+k)+1 := by ac_rfl
      rw [hbaseEq] at ih1
      rw [ih1]
    · intro a ha ih k hk hbound hscope
      have hle : a+1 ≤ ^∃ a := by
        change a+1 ≤ pair (7 : M) a+1
        simpa only [add_comm] using add_le_add_right (le_pair_right (7 : M) a) 1
      have hA : a+(k+1) ≤ K := le_trans (by
        have hh := add_le_add_right hle k
        simpa only [add_assoc,add_comm,add_left_comm] using hh) hbound
      have hk1 : k+1 ≤ K := le_trans (by
        have hz : (0 : M) ≤ a := zero_le
        simpa only [zero_add,add_comm] using add_le_add_right hz (k+1)) hA
      have hka : k < K := lt_iff_succ_le.mpr hk1
      have hsa : IsSemiformula SourceL ((k+1)+1) a := by simpa only [IsSemiformula.exs] using hscope
      have ih1 := ih (k+1) hk1 hA hsa
      rw [depthSourceOpening_eq] at ih1 ⊢
      rw [sourceOpeningFormula_ex K s k a hs hl hka ha,
        fixedFormulaTranslation_ex _ _ _ _ _ (sourceOpeningFormula_valid K s (k+1) a hs hl hk1 hsa).isUFormula,
        fixedFormulaTranslation_ex _ _ _ _ _ ha]
      rw [allocateBound_succ,allocateBound_succ] at ih1
      have hbaseEq : base+1+(k+1) = (base+1+k)+1 := by ac_rfl
      rw [hbaseEq] at ih1
      rw [ih1]
  have h0 := hall p hp.isUFormula 0 (show (0 : M) ≤ K from zero_le) (by simp [K]) (by simpa using hp)
  rw [depthSourceOpening_eq] at h0
  have hs0 := sourceQVec_trace_start (?[ ^&(0 : M)] : M) s hs
  unfold FreeBridge
  simpa only [sourceOpeningFormula,hs0,LO.FirstOrder.Arithmetic.Bootstrapping.free,substs1,allocateBound_zero,add_zero] using h0

/-- Complete universal-introduction field for arbitrary valid source formulas. -/
theorem simRuleAll_general (e s p : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e) (LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL p)) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ p)) 1)) := by
  have hp : IsSemiformula SourceL 1 p := by
    have h := hs _ hm
    simpa only [IsSemiformula.all,zero_add] using h
  exact simRuleAll_of_bridge e s p hs hm
    (sourceOpening_freeBridge p (simBound e) (simFree e) (simBase e) (simReserve e) hp)

#print axioms simRuleAll_general
#print axioms sourceOpening_freeBridge
end models
end PA194ModelLogic
