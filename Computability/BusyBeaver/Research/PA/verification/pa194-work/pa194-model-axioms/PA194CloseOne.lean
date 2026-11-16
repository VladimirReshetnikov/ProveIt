import PA194BoundSeparation
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
local instance repeatSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance repeatSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance repeatSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance repeatSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance repeatSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance repeatSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Bind free variable zero in an internal formula. -/
noncomputable def closeOne (p : M) : M := ^∀ (bindFormula 0 p)

theorem closeOne_scoped (p : M) (hp : IsSemiformula SourceL 0 p) :
    IsSemiformula SourceL 0 (closeOne p) := by
  have h := (bindFormula_scope_open p hp).1
  simpa only [closeOne, IsSemiformula.all, zero_add] using h

theorem closeOne_definable : 𝚺₁-Function₁ (closeOne : M → M) := by
  haveI : 𝚺₁-Function₂ (bindFormula : M → M → M) := bindFormula_definable
  unfold closeOne
  definability

/-- Lift an arbitrary target theorem across a newly bound free parameter. -/
theorem closeOne_leaf (e p : M) (hp : IsSemiformula SourceL 0 p)
    (ht : numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr (simPushFree e) p) 1)) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (closeOne p)) 1) := by
  have hscope := closeOne_scoped p hp
  have hs : IsFormulaSet SourceL ({closeOne p} : M) := singletonFormulaSet _ hscope
  have hm : closeOne p ∈ ({closeOne p} : M) := mem_singleton_iff.mpr rfl
  have hopen := (bindFormula_scope_open p hp).2
  have hg := simRuleAll_general e ({closeOne p} : M) (bindFormula 0 p) hs hm
  rw [hopen] at hg
  exact tp_mp (tp_gen (simBase e) ht) hg

/-- Externally indexed iteration; the index is a standard Lean natural number. -/
noncomputable def closeIter : Nat → M → M
  | 0, p => p
  | n+1, p => closeOne (closeIter n p)

noncomputable def pushIter : Nat → M → M
  | 0, e => e
  | n+1, e => pushIter n (simPushFree e)

theorem closeIter_scoped (n : Nat) (p : M) (hp : IsSemiformula SourceL 0 p) :
    IsSemiformula SourceL 0 (closeIter n p) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact closeOne_scoped _ ih

theorem closeIter_leaf (n : Nat) (e p : M) (hp : IsSemiformula SourceL 0 p)
    (ht : numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr (pushIter n e) p) 1)) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (closeIter n p)) 1) := by
  induction n generalizing e with
  | zero => exact ht
  | succ n ih =>
    apply closeOne_leaf e (closeIter n p) (closeIter_scoped n p hp)
    exact ih (simPushFree e) ht

#print axioms closeIter_leaf
#print axioms closeIter_scoped
#print axioms closeOne_leaf
#print axioms closeOne_scoped
#print axioms closeOne_definable
end models
end PA194BindSource
