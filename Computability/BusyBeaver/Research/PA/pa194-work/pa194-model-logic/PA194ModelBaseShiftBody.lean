import PA194ModelBaseShiftStack
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
local instance baseShiftBodyZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance baseShiftBodyOne : One M := ⟨F oneCode Fin.elim0⟩
local instance baseShiftBodyAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance baseShiftBodyMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance baseShiftBodyLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance baseShiftBodyIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- The common quantifier step in the general base-shift induction. -/
theorem baseShift_binderBodies (initial free base reserve K k p : M)
    (hp : IsUFormula SourceL p) (hk : k ≤ K) (hpk : p+(k+1) ≤ K)
    (hinit : ∀ i ≤ K, initial.[i] < base) (hfree : ∀ i ≤ K, free.[i] < base)
    (hreserve : base+K+2 < reserve)
    (ih : depthBaseShift initial free base reserve p (k+1)) :
    let w := base+k
    let y := w+1
    let stack := F allocateBound ![k,base,initial]
    let A := F fixedFormulaTranslation ![p,pair w stack+1,free,w+1,reserve]
    let C := F fixedFormulaTranslation ![p,pair y stack+1,free,y+1,reserve]
    TargetEquiv (allValue w A) (allValue y C) ∧ TargetEquiv (exValue w A) (exValue y C) := by
  dsimp only
  let w := base+k
  let y := w+1
  let stack := F allocateBound ![k,base,initial]
  let A := F fixedFormulaTranslation ![p,pair w stack+1,free,w+1,reserve]
  let B := F fixedFormulaTranslation ![p,pair w stack+1,free,y+1,reserve]
  let C := F fixedFormulaTranslation ![p,pair y stack+1,free,y+1,reserve]
  have hpK : p ≤ K := by
    have hh := add_le_add_right (zero_le : (0 : M) ≤ k+1) p
    exact le_trans (by simpa only [zero_add,add_zero,add_comm] using hh) hpk
  have hwK : w ≤ base+K := by
    dsimp only [w]
    simpa only [add_comm] using add_le_add_right hk base
  have hbaseK : base ≤ base+K := le_self_add
  have hslack : base+K+1 < reserve := by
    have h := lt_add_one (base+K+1)
    have heq : (base+K+1)+1 = base+K+2 := by norm_num [add_assoc]
    rw [heq] at h
    exact lt_trans h hreserve
  have hwRes : w < reserve :=
    lt_of_le_of_lt hwK (lt_trans (lt_add_one (base+K)) hslack)
  have hyRes : y < reserve := by
    have hh := add_le_add_right hwK 1
    have hyK : y ≤ base+K+1 := by
      dsimp only [y]
      simpa only [add_comm] using hh
    exact lt_of_le_of_lt hyK hslack
  have hbaseRes : base < reserve := lt_of_le_of_lt hbaseK (lt_trans (lt_add_one (base+K)) hslack)
  have hcommon : (y+1)+p < reserve := by
    have hh := add_le_add_right (add_le_add_right hpk base) 1
    have hle : (y+1)+p ≤ base+K+1 := by
      dsimp only [y,w]
      simpa only [add_assoc,add_comm,add_left_comm] using hh
    exact lt_of_le_of_lt hle hslack
  have hinitRes : ∀ i ≤ K, initial.[i] < reserve := by
    intro i hi; exact lt_trans (hinit i hi) hbaseRes
  have hfreeRes : ∀ i ≤ p, free.[i] < reserve := by
    intro i hi; exact lt_trans (hfree i (le_trans hi hpK)) hbaseRes
  have hstackResK : ∀ i ≤ K, stack.[i] < reserve :=
    allocatedBound_labels K base initial reserve (le_of_lt (lt_trans (lt_add_one (base+K)) hslack)) hinitRes k hk
  have hstackBeforeK : ∀ i ≤ K, stack.[i] < w :=
    allocatedBound_beforeCurrent K base initial k hinit hk
  have hstackRes : ∀ i ≤ p, stack.[i] < reserve := fun i hi => hstackResK i (le_trans hi hpK)
  have hstackBefore : ∀ i ≤ p, stack.[i] < w := fun i hi => hstackBeforeK i (le_trans hi hpK)
  have hfreeBefore : ∀ i ≤ p, free.[i] < w := by
    intro i hi
    have hb : base ≤ w := by dsimp only [w]; exact le_self_add
    exact lt_of_lt_of_le (hfree i (le_trans hi hpK)) hb
  have hobs : TargetPremiseRewrite (neighborhoodValue y w reserve) B C :=
    observationalRewrite_all_codes w y p (pair w stack+1) (pair y stack+1) free (y+1) reserve hp
      (lt_trans (lt_add_one w) (lt_add_one y)) (lt_add_one y) hcommon
      (pushLabels_aligned w y stack p)
      (pushLabels_below w stack p reserve hwRes hstackRes)
      (pushLabels_below y stack p reserve hyRes hstackRes) hfreeRes
  have havB : ∀ i ≤ p, (pair w stack+1).[i] ≠ y :=
    pushLabels_avoid w stack p y (ne_of_lt (lt_add_one w))
      (fun i hi => ne_of_lt (lt_trans (hstackBefore i hi) (lt_add_one w)))
  have havC : ∀ i ≤ p, (pair y stack+1).[i] ≠ w :=
    pushLabels_avoid y stack p w (ne_of_gt (lt_add_one w))
      (fun i hi => ne_of_lt (hstackBefore i hi))
  have hfY : ∀ i ≤ p, free.[i] ≠ y :=
    fun i hi => ne_of_lt (lt_trans (hfreeBefore i hi) (lt_add_one w))
  have hfW : ∀ i ≤ p, free.[i] ≠ w := fun i hi => ne_of_lt (hfreeBefore i hi)
  have hvB := generalVacuity_below_all_codes y p (pair w stack+1) free (y+1) reserve hp
    (lt_add_one y) havB hfY (ne_of_lt hyRes)
  have hvC := generalVacuity_below_all_codes w p (pair y stack+1) free (y+1) reserve hp
    (lt_trans (lt_add_one w) (lt_add_one y)) havC hfW (ne_of_lt hwRes)
  unfold GeneralVacuity at hvB hvC
  simp only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] at hvB hvC
  rw [depthBaseShift_eq] at ih
  rw [allocateBound_succ] at ih
  have hbaseEq : base+(k+1) = w+1 := by dsimp only [w]; ac_rfl
  rw [hbaseEq] at ih
  have ih' : TargetEquiv A B := by simpa only [A,B,y,stack] using ih
  exact ⟨crossBinder_all w y reserve A B C (ne_of_gt hwRes) (ne_of_gt hyRes) ih'.1 ih'.2 hobs hvB hvC,
    crossBinder_ex w y reserve A B C (ne_of_gt hwRes) (ne_of_gt hyRes) ih'.1 ih'.2 hobs hvB hvC⟩

#print axioms baseShift_binderBodies
end models
end PA194ModelLogic
