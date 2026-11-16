import PA194ModelSourceSubstAtom
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

/-! Internal source substitution at arbitrary binder depth. -/
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
local instance sourceSubstGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceSubstGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceSubstGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceSubstGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceSubstGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceSubstGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem sourceSubstFormula_valid (limit s k p witness : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&witness] : M)] s)
    (hl : limit + 1 = lh s) (hk : k ≤ limit)
    (hp : IsSemiformula SourceL (k+1) p) :
    IsSemiformula SourceL k (sourceSubstFormula s k p) := by
  exact hp.subst (sourceSubstQVec_trace_typed limit s witness h hl k hk)

theorem sourceSubstFormula_and (s k a b : M) (ha : IsUFormula SourceL a) (hb : IsUFormula SourceL b) :
    sourceSubstFormula s k (a ^⋏ b) = sourceSubstFormula s k a ^⋏ sourceSubstFormula s k b := by
  simp only [sourceSubstFormula,substs_and ha hb]

theorem sourceSubstFormula_or (s k a b : M) (ha : IsUFormula SourceL a) (hb : IsUFormula SourceL b) :
    sourceSubstFormula s k (a ^⋎ b) = sourceSubstFormula s k a ^⋎ sourceSubstFormula s k b := by
  simp only [sourceSubstFormula,substs_or ha hb]

theorem sourceSubstFormula_all (limit s k a witness : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&witness] : M)] s)
    (hl : limit + 1 = lh s) (hk : k < limit) (ha : IsUFormula SourceL a) :
    sourceSubstFormula s k (^∀ a) = ^∀ (sourceSubstFormula s (k+1) a) := by
  rw [sourceSubstFormula,substs_all ha,
    ← sourceQVec_trace_step _ limit s k h hl hk]
  rfl

theorem sourceSubstFormula_ex (limit s k a witness : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![(?[ ^&witness] : M)] s)
    (hl : limit + 1 = lh s) (hk : k < limit) (ha : IsUFormula SourceL a) :
    sourceSubstFormula s k (^∃ a) = ^∃ (sourceSubstFormula s (k+1) a) := by
  rw [sourceSubstFormula,substs_ex ha,
    ← sourceQVec_trace_step _ limit s k h hl hk]
  rfl

noncomputable def depthSourceSubst (s bound free base witness reserve p k : M) : Prop :=
  positiveTranslation (depthEnvironment bound (free) base reserve k) (sourceSubstFormula s k p) =
    positiveTranslation (depthEnvironment (pair (free.[witness]) bound+1) free base reserve k) p

theorem depthSourceSubst_definable (s bound free base witness reserve : M) :
    𝚺₁-Relation (depthSourceSubst s bound free base witness reserve) := by
  haveI : 𝚺₁-Function₂ (positiveTranslation : M → M → M) :=
    (positiveTr (M := M)).tr_defined.to_definable
  haveI : 𝚺₁-Function₂ (fun (p k : M) => sourceSubstFormula s k p) := by
    unfold sourceSubstFormula
    definability
  haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base,bound]) :=
    PA194CodeInstance.unary_of_three allocateBound base bound
  haveI : 𝚺₁-Function₁ (fun k : M => F allocateBound ![k,base,pair (free.[witness]) bound+1]) :=
    PA194CodeInstance.unary_of_three allocateBound base (pair (free.[witness]) bound+1)
  haveI : 𝚺₁-Function₁ (depthEnvironment bound (free) base reserve) := by
    unfold depthEnvironment; definability
  haveI : 𝚺₁-Function₁ (depthEnvironment (pair (free.[witness]) bound+1) free base reserve) := by
    unfold depthEnvironment; definability
  unfold depthSourceSubst
  definability

theorem depthSourceSubst_eq (s bound free base witness reserve p k : M) :
    depthSourceSubst s bound free base witness reserve p k ↔
      F fixedFormulaTranslation ![sourceSubstFormula s k p,F allocateBound ![k,base,bound],
        free,base+k,reserve] =
      F fixedFormulaTranslation ![p,F allocateBound ![k,base,pair (free.[witness]) bound+1],free,base+k,reserve] := by
  unfold depthSourceSubst depthEnvironment
  rw [positiveTranslation_model,positiveTranslation_model]

/-- Exact source substitution through arbitrary nonstandard quantifier depth. -/
theorem sourceSubst_translation (p bound free base witness reserve : M)
    (hp : IsSemiformula SourceL 1 p) :
    F fixedFormulaTranslation ![substs1 SourceL (^&witness) p,bound,free,base,reserve] =
      F fixedFormulaTranslation ![p,pair (free.[witness]) bound+1,free,base,reserve] := by
  let K := p
  obtain ⟨s,hs,hl⟩ := sourceQVec_exists_trace (?[ ^&witness] : M) K
  haveI : 𝚺₁-Relation (depthSourceSubst s bound free base witness reserve) :=
    depthSourceSubst_definable s bound free base witness reserve
  have hdef : 𝚺₁-Predicate (fun q : M => ∀ k ≤ K, q+k ≤ K → IsSemiformula SourceL (k+1) q →
      depthSourceSubst s bound free base witness reserve q k) := by definability
  have hall : ∀ q, IsUFormula SourceL q → ∀ k ≤ K, q+k ≤ K → IsSemiformula SourceL (k+1) q →
      depthSourceSubst s bound free base witness reserve q k := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv k hk hbound hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.rel.mp hscope).2
      rw [depthSourceSubst_eq]
      exact sourceSubst_positiveAtom K s k r a b bound free base witness reserve hs hl hk hr hsa hsb
    · intro arity r v hr hv k hk hbound hscope
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
      obtain ⟨hsa,hsb⟩ := IsSemitermVec.doubleton.mp (IsSemiformula.nrel.mp hscope).2
      rw [depthSourceSubst_eq]
      exact sourceSubst_negativeAtom K s k r a b bound free base witness reserve hs hl hk hr hsa hsb
    · intro k hk hbound hscope
      rw [depthSourceSubst_eq]
      simp only [sourceSubstFormula,substs_verum]
      rw [fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
    · intro k hk hbound hscope
      rw [depthSourceSubst_eq]
      simp only [sourceSubstFormula,substs_falsum]
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
      rw [depthSourceSubst_eq] at ih1 ih2 ⊢
      rw [sourceSubstFormula_and s k a b ha hb,
        fixedFormulaTranslation_and _ _ _ _ _ _ (sourceSubstFormula_valid K s k a witness hs hl hk hsa).isUFormula (sourceSubstFormula_valid K s k b witness hs hl hk hsb).isUFormula,
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
      rw [depthSourceSubst_eq] at ih1 ih2 ⊢
      rw [sourceSubstFormula_or s k a b ha hb,
        fixedFormulaTranslation_or _ _ _ _ _ _ (sourceSubstFormula_valid K s k a witness hs hl hk hsa).isUFormula (sourceSubstFormula_valid K s k b witness hs hl hk hsb).isUFormula,
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
      rw [depthSourceSubst_eq] at ih1 ⊢
      rw [sourceSubstFormula_all K s k a witness hs hl hka ha,
        fixedFormulaTranslation_all _ _ _ _ _ (sourceSubstFormula_valid K s (k+1) a witness hs hl hk1 hsa).isUFormula,
        fixedFormulaTranslation_all _ _ _ _ _ ha]
      rw [allocateBound_succ,allocateBound_succ] at ih1
      have hbaseEq : base+(k+1) = (base+k)+1 := by ac_rfl
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
      rw [depthSourceSubst_eq] at ih1 ⊢
      rw [sourceSubstFormula_ex K s k a witness hs hl hka ha,
        fixedFormulaTranslation_ex _ _ _ _ _ (sourceSubstFormula_valid K s (k+1) a witness hs hl hk1 hsa).isUFormula,
        fixedFormulaTranslation_ex _ _ _ _ _ ha]
      rw [allocateBound_succ,allocateBound_succ] at ih1
      have hbaseEq : base+(k+1) = (base+k)+1 := by ac_rfl
      rw [hbaseEq] at ih1
      rw [ih1]
  have h0 := hall p hp.isUFormula 0 (show (0 : M) ≤ K from zero_le) (by simp [K]) (by simpa using hp)
  rw [depthSourceSubst_eq] at h0
  have hs0 := sourceQVec_trace_start (?[ ^&witness] : M) s hs
  simpa only [sourceSubstFormula,hs0,substs1,allocateBound_zero,add_zero] using h0

#print axioms sourceSubst_translation
end models
end PA194ModelLogic
