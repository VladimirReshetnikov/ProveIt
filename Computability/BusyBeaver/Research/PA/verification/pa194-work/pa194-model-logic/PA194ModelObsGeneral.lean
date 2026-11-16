import PA194ModelObsSteps
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
local instance obsGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance obsGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance obsGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance obsGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance obsGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance obsGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Observational equality transports every internally valid source formula
through aligned bound stacks, including nonstandard syntax and binder depth. -/
theorem observationalRewrite_all_codes (x y p initial₁ initial₂ free base reserve : M)
    (hp : IsUFormula SourceL p) (hx : x < base) (hy : y < base)
    (hbase : base+p < reserve)
    (halign : ∀ i ≤ p, LabelAligned x y initial₁.[i] initial₂.[i])
    (hinit₁ : ∀ i ≤ p, initial₁.[i] < reserve)
    (hinit₂ : ∀ i ≤ p, initial₂.[i] < reserve)
    (hfree : ∀ i ≤ p, free.[i] < reserve) :
    TargetPremiseRewrite (neighborhoodValue y x reserve)
      (F fixedFormulaTranslation ![p,initial₁,free,base,reserve])
      (F fixedFormulaTranslation ![p,initial₂,free,base,reserve]) := by
  let K := p
  have hzbase : base ≤ reserve := le_of_lt (lt_of_le_of_lt (show base ≤ base+K from le_self_add) hbase)
  have hzx : reserve ≠ x := ne_of_gt (lt_of_lt_of_le hx hzbase)
  have hzy : reserve ≠ y := ne_of_gt (lt_of_lt_of_le hy hzbase)
  haveI : 𝚺₁-Relation (depthObsRewrite x y initial₁ initial₂ free base reserve) :=
    depthObsRewrite_definable x y initial₁ initial₂ free base reserve
  have hdef : 𝚺₁-Predicate (fun q : M => ∀ k ≤ K, q+k ≤ K →
      depthObsRewrite x y initial₁ initial₂ free base reserve q k) := by definability
  have hall : ∀ q, IsUFormula SourceL q → ∀ k ≤ K, q+k ≤ K →
      depthObsRewrite x y initial₁ initial₂ free base reserve q k := by
    intro q hq
    apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ q hq
    · intro arity r v hr hv k hk hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hqK : (^rel (2 : M) r v) ≤ K := by
        have hh := add_le_add_right (zero_le : (0 : M) ≤ k) (^rel (2 : M) r v)
        exact le_trans (by simpa only [zero_add,add_comm] using hh) hbound
      have hh := depthObsRewrite_atom x y initial₁ initial₂ free base reserve K k 0 r v hr hv (Or.inl rfl)
        (by simpa only [qqRel] using hqK) hk (le_of_lt hbase) halign hinit₁ hinit₂ hfree hzy hzx
      simpa only [ite_true] using hh
    · intro arity r v hr hv k hk hbound
      have har := PA194AtomShiftCodeModel.sourceRelation_arity hr
      subst arity
      have hqK : (^nrel (2 : M) r v) ≤ K := by
        have hh := add_le_add_right (zero_le : (0 : M) ≤ k) (^nrel (2 : M) r v)
        exact le_trans (by simpa only [zero_add,add_comm] using hh) hbound
      have hh := depthObsRewrite_atom x y initial₁ initial₂ free base reserve K k 1 r v hr hv (Or.inr rfl)
        (by simpa only [qqNRel] using hqK) hk (le_of_lt hbase) halign hinit₁ hinit₂ hfree hzy hzx
      simpa only [Arithmetic.one_ne_zero,ite_false] using hh
    · intro k hk hbound
      exact depthObsRewrite_verum _ _ _ _ _ _ _ _
    · intro k hk hbound
      exact depthObsRewrite_falsum _ _ _ _ _ _ _ _
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋏ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      exact depthObsRewrite_and _ _ _ _ _ _ _ _ a b ha hb (iha k hk hA) (ihb k hk hB)
    · intro a b ha hb iha ihb k hk hbound
      have hleA : a ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hleB : b ≤ a ^⋎ b := le_of_lt <| lt_of_le_of_lt
        (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (lt_add_one _)
      have hA : a+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleA k) hbound
      have hB : b+k ≤ K := le_trans (by simpa only [add_comm] using add_le_add_right hleB k) hbound
      exact depthObsRewrite_or _ _ _ _ _ _ _ _ a b ha hb (iha k hk hA) (ihb k hk hB)
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
      have hb : base ≤ base+k := by
        simpa only [add_comm,zero_add,add_zero] using add_le_add_right (zero_le : (0 : M) ≤ k) base
      have hbK : base+k ≤ base+K := by simpa only [add_comm] using add_le_add_right hk base
      exact depthObsRewrite_all _ _ _ _ _ _ _ k a ha
        (ne_of_gt (lt_of_lt_of_le hy hb)) (ne_of_gt (lt_of_lt_of_le hx hb))
        (ne_of_lt (lt_of_le_of_lt hbK hbase)) (ih (k+1) hk1 hA)
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
      have hb : base ≤ base+k := by
        simpa only [add_comm,zero_add,add_zero] using add_le_add_right (zero_le : (0 : M) ≤ k) base
      have hbK : base+k ≤ base+K := by simpa only [add_comm] using add_le_add_right hk base
      exact depthObsRewrite_ex _ _ _ _ _ _ _ k a ha
        (ne_of_gt (lt_of_lt_of_le hy hb)) (ne_of_gt (lt_of_lt_of_le hx hb))
        (ne_of_lt (lt_of_le_of_lt hbK hbase)) (ih (k+1) hk1 hA)
  have h0 := hall p hp 0 (show (0 : M) ≤ K from zero_le) (by simp [K])
  rw [depthObsRewrite_eq] at h0
  simpa only [allocateBound_zero,add_zero] using h0

#print axioms observationalRewrite_all_codes
end models
end PA194ModelLogic
