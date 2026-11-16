import PA194ModelObsInduction
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
local instance obsAtomDepthZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance obsAtomDepthOne : One M := ⟨F oneCode Fin.elim0⟩
local instance obsAtomDepthAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance obsAtomDepthMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance obsAtomDepthLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance obsAtomDepthIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- The atomic step of the depth-indexed observational transport. -/
theorem depthObsRewrite_atom (x y initial₁ initial₂ free base reserve K k tag r v : M)
    (hr : SourceL.IsRel 2 r) (hv : IsUTermVec SourceL 2 v) (htag : tag = 0 ∨ tag = 1)
    (hatom : pair tag (pair 2 (pair r v))+1 ≤ K) (hk : k ≤ K) (hbase : base+K ≤ reserve)
    (halign : ∀ i ≤ K, LabelAligned x y initial₁.[i] initial₂.[i])
    (hinit₁ : ∀ i ≤ K, initial₁.[i] < reserve) (hinit₂ : ∀ i ≤ K, initial₂.[i] < reserve)
    (hfree : ∀ i ≤ K, free.[i] < reserve) (hzy : reserve ≠ y) (hzx : reserve ≠ x) :
    if tag = 0 then depthObsRewrite x y initial₁ initial₂ free base reserve (^rel (2 : M) r v) k
    else depthObsRewrite x y initial₁ initial₂ free base reserve (^nrel (2 : M) r v) k := by
  obtain ⟨a,b,ha,hb,rfl⟩ := IsUTermVec.two_iff.mp hv
  have hvlt := vector_lt_atom tag r (pair a (pair b 0+1)+1)
  have haK : a ≤ K := le_trans (le_of_lt (lt_trans (pairVector_term_lt a b).1 hvlt)) hatom
  have hbK : b ≤ K := le_trans (le_of_lt (lt_trans (pairVector_term_lt a b).2 hvlt)) hatom
  have hal := allocatedBound_aligned K base initial₁ initial₂ x y halign k hk
  have hb₁ := allocatedBound_labels K base initial₁ reserve hbase hinit₁ k hk
  have hb₂ := allocatedBound_labels K base initial₂ reserve hbase hinit₂ k hk
  rcases htag with rfl | rfl
  · simp only [ite_true,depthObsRewrite_eq]
    exact observationalPositiveAtom_bounded x y r a b _ _ free (base+k) reserve K
      hr ha hb haK hbK hal hb₁ hb₂ hfree hzy hzx
  · simp only [Arithmetic.one_ne_zero,ite_false,depthObsRewrite_eq]
    exact observationalNegativeAtom_bounded x y r a b _ _ free (base+k) reserve K
      hr ha hb haK hbK hal hb₁ hb₂ hfree hzy hzx

#print axioms depthObsRewrite_atom
end models
end PA194ModelLogic
