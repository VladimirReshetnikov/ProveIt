import PA194ModelBaseShiftBody
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
local instance baseShiftGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance baseShiftGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance baseShiftGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance baseShiftGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance baseShiftGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance baseShiftGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- General one-step binder-base conversion for arbitrary internally valid
source formulas, including nonstandard syntax and nested quantifiers. -/
theorem generalBaseShift_all_codes (p initial free base reserve : M)
    (hp : IsUFormula SourceL p)
    (hinit : ∀ i ≤ p, initial.[i] < base) (hfree : ∀ i ≤ p, free.[i] < base)
    (hreserve : base+p+2 < reserve) :
    TargetEquiv (F fixedFormulaTranslation ![p,initial,free,base,reserve])
      (F fixedFormulaTranslation ![p,initial,free,base+1,reserve]) := by
  let K := p
  haveI : 𝚺₁-Relation (depthBaseShift initial free base reserve) :=
    depthBaseShift_definable initial free base reserve
  have hdef : 𝚺₁-Predicate (fun q : M => ∀ k ≤ K, q+k ≤ K →
      depthBaseShift initial free base reserve q k) := by definability
  have hall : ∀ q, IsUFormula SourceL q → ∀ k ≤ K, q+k ≤ K →
      depthBaseShift initial free base reserve q k := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv k hk hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      rw [depthBaseShift_eq]
      rw [positiveAtom_base_irrelevant r v _ _ _ _ _ hr hv]
      exact targetEquiv_refl _
    · intro arity r v hr hv k hk hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      rw [depthBaseShift_eq]
      rw [fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
        fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,
        positiveAtom_base_irrelevant r v _ _ _ _ _ hr hv]
      exact targetEquiv_refl _
    · intro k hk hbound
      rw [depthBaseShift_eq,fixedFormulaTranslation_verum,fixedFormulaTranslation_verum]
      exact targetEquiv_refl _
    · intro k hk hbound
      rw [depthBaseShift_eq,fixedFormulaTranslation_falsum,fixedFormulaTranslation_falsum]
      exact targetEquiv_refl _
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA
      have ih2 := ihb k hk hB
      rw [depthBaseShift_eq] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_and _ _ _ _ _ _ ha hb,fixedFormulaTranslation_and _ _ _ _ _ _ ha hb]
      exact targetEquiv_and _ _ _ _ ih1 ih2
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      have ih1 := iha k hk hA
      have ih2 := ihb k hk hB
      rw [depthBaseShift_eq] at ih1 ih2 ⊢
      rw [fixedFormulaTranslation_or _ _ _ _ _ _ ha hb,fixedFormulaTranslation_or _ _ _ _ _ _ ha hb]
      exact targetEquiv_or _ _ _ _ ih1 ih2
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
      have hstep := baseShift_binderBodies initial free base reserve K k a ha hk hA hinit hfree hreserve (ih (k+1) hk1 hA)
      rw [depthBaseShift_eq,fixedFormulaTranslation_all _ _ _ _ _ ha,fixedFormulaTranslation_all _ _ _ _ _ ha]
      exact hstep.1
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
      have hstep := baseShift_binderBodies initial free base reserve K k a ha hk hA hinit hfree hreserve (ih (k+1) hk1 hA)
      rw [depthBaseShift_eq,fixedFormulaTranslation_ex _ _ _ _ _ ha,fixedFormulaTranslation_ex _ _ _ _ _ ha]
      exact hstep.2
  have h0 := hall p hp 0 (show (0 : M) ≤ K from zero_le) (by simp [K])
  rw [depthBaseShift_eq] at h0
  simpa only [allocateBound_zero,add_zero] using h0

#print axioms generalBaseShift_all_codes
end models
end PA194ModelLogic
