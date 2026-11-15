import PA194FullyClosedSeparation
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance uncloseOnceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance uncloseOnceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance uncloseOnceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance uncloseOnceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance uncloseOnceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance uncloseOnceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Remove the outer all binder and reopen its first bound variable. -/
noncomputable def uncloseOnce (q : M) : M :=
  LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL (pi₂ (q-1))

theorem uncloseOnce_closeOne (p : M) (hp : IsSemiformula SourceL 0 p) :
    uncloseOnce (closeOne p) = p := by
  unfold uncloseOnce closeOne qqAll
  simp only [add_tsub_cancel_right,pi₂_pair]
  exact (bindFormula_scope_open p hp).2

theorem uncloseOnce_modelClose_succ (n p : M) (hp : IsSemiformula SourceL 0 p) :
    uncloseOnce (modelClose (n+1) p) = modelClose n p := by
  rw [modelClose_succ]
  exact uncloseOnce_closeOne _ (modelClose_scope n p hp)

theorem le_qqAnd_left (a b : M) : a ≤ a ^⋏ b := by
  change a ≤ pair (4 : M) (pair a b) + 1
  exact le_trans (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (le_of_lt (lt_add_one _))
theorem le_qqAnd_right (a b : M) : b ≤ a ^⋏ b := by
  change b ≤ pair (4 : M) (pair a b) + 1
  exact le_trans (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (le_of_lt (lt_add_one _))
theorem le_qqOr_left (a b : M) : a ≤ a ^⋎ b := by
  change a ≤ pair (5 : M) (pair a b) + 1
  exact le_trans (le_trans (le_pair_left a b) (le_pair_right (5 : M) (pair a b))) (le_of_lt (lt_add_one _))
theorem le_qqOr_right (a b : M) : b ≤ a ^⋎ b := by
  change b ≤ pair (5 : M) (pair a b) + 1
  exact le_trans (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (le_of_lt (lt_add_one _))
theorem le_qqAll (a : M) : a ≤ ^∀ a := by
  change a ≤ pair (6 : M) a + 1
  exact le_trans (le_pair_right (6 : M) a) (le_of_lt (lt_add_one _))
theorem le_qqExs (a : M) : a ≤ ^∃ a := by
  change a ≤ pair (7 : M) a + 1
  exact le_trans (le_pair_right (7 : M) a) (le_of_lt (lt_add_one _))

theorem sepRoot_contains_property (φ : M) : φ ≤ sepRoot φ := by
  unfold sepRoot sepInner
  apply le_trans (le_qqAnd_right _ φ)
  apply le_trans (le_qqOr_right _ _)
  apply le_trans (le_qqAnd_left _ _)
  apply le_trans (le_qqAll _)
  apply le_trans (le_qqExs _)
  exact le_qqAll _

#print axioms sepRoot_contains_property
#print axioms uncloseOnce_closeOne
#print axioms uncloseOnce_modelClose_succ
end models
end PA194BindSource
