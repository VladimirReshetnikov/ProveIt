import PA194ModelFormulaFreshness

/-! Bounded internal induction for freshness of reconstructed bound-label stacks.
The bound is explicit; free-variable environment hypotheses and semantic validity
of translated formulas remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubAddition
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def stageLabelBound (stage : M → M) (reserve : M) (n i : M) : Prop := (stage n).[i] < reserve

theorem stageLabelBound_definable (stage : M → M) (reserve : M)
    (hs : 𝚺₁-Function₁ stage) : 𝚺₁-Relation (stageLabelBound stage reserve) := by
  haveI := hs
  unfold stageLabelBound
  definability

def stageBounds (stage : M → M) (ceiling reserve : M) (n : M) : Prop :=
  ∀ i ≤ ceiling, stageLabelBound stage reserve n i

theorem stageBounds_definable (stage : M → M) (ceiling reserve : M)
    (hs : 𝚺₁-Function₁ stage) : 𝚺₁-Predicate (stageBounds stage ceiling reserve) := by
  haveI := stageLabelBound_definable stage reserve hs
  unfold stageBounds
  definability

theorem boundedStageInvariant_definable (stage : M → M) (ceiling reserve : M)
    (hs : 𝚺₁-Function₁ stage) : 𝚺₁-Predicate (fun n : M =>
      n ≤ ceiling → stageBounds stage ceiling reserve n) := by
  haveI := stageBounds_definable stage ceiling reserve hs
  definability

theorem allocatedBound_labels (ceiling base initial reserve : M)
    (hreserve : base+ceiling ≤ reserve)
    (hinit : ∀ i ≤ ceiling, initial.[i] < reserve) (n : M) (hn : n ≤ ceiling) :
    ∀ i ≤ ceiling, (F allocateBound ![n,base,initial]).[i] < reserve := by
  let stage : M → M := fun n => F allocateBound ![n,base,initial]
  have hdef := boundedStageInvariant_definable stage ceiling reserve
    (PA194CodeInstance.unary_of_three allocateBound base initial)
  have hall : ∀ n : M, n ≤ ceiling → stageBounds stage ceiling reserve n := by
    intro n
    induction n using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _ i hi
      change (F allocateBound ![0,base,initial]).[i] < reserve
      rw [allocateBound_zero]
      exact hinit i hi
    case succ n ih =>
      intro hn i hi
      have hn' : n ≤ ceiling := le_trans (le_of_lt (lt_add_one n)) hn
      have hlt : base+n < reserve := by
        have hnlt : n < ceiling := lt_of_lt_of_le (lt_add_one n) hn
        exact lt_of_lt_of_le (by simpa only [add_comm] using add_lt_add_left hnlt base) hreserve
      change (F allocateBound ![n+1,base,initial]).[i] < reserve
      rw [allocateBound_succ]
      rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
      · rw [nth_zero]
        simpa [fstIdx] using hlt
      · rw [nth_succ]
        have hj : j ≤ ceiling := le_trans (le_of_lt (lt_add_one j)) hi
        have hp := ih hn' j hj
        change (F allocateBound ![n,base,initial]).[j] < reserve at hp
        simpa [sndIdx] using hp
  exact hall n hn

#print axioms stageLabelBound_definable
#print axioms stageBounds_definable
#print axioms boundedStageInvariant_definable
#print axioms allocatedBound_labels
end models
end PA194ModelLogic
