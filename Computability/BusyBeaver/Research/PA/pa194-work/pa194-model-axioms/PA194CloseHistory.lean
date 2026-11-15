import PA194CloseOne
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
local instance repeatHistoryZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance repeatHistoryOne : One M := ⟨F oneCode Fin.elim0⟩
local instance repeatHistoryAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance repeatHistoryMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance repeatHistoryLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance repeatHistoryIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Fixed arithmetic graph for one binding step. -/
noncomputable def closeOneStepDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index seed. ∃ body, !(FormulaClose.blueprint.result SourceL) body 0 previous ∧ !qqAllDef out body”
noncomputable def closeIterBlueprint : PR.Blueprint 1 where
  zero := sourceQVecZeroDef
  succ := closeOneStepDef
noncomputable def closeIterConstruction : PR.Construction M closeIterBlueprint where
  zero p := p 0
  succ _ _ previous := closeOne previous
  zero_defined := .mk fun e => by simp [closeIterBlueprint,sourceQVecZeroDef]
  succ_defined := .mk fun e => by
    simp [closeIterBlueprint,closeOneStepDef,closeOne,bindFormula,
      FormulaClose.construction.result_defined.defined]

theorem closeIter_exists_trace (seed limit : M) :
    ∃ s : M, (closeIterConstruction (M := M)).CSeq ![seed] s ∧ limit + 1 = lh s :=
  PR.Construction.CSeq.exists _ _ _

theorem closeIter_trace_start (seed s : M) (h : (closeIterConstruction (M := M)).CSeq ![seed] s) :
    znth s 0 = seed := by
  have hm := h.zero
  have hm' : ⟪(0 : M), seed⟫ ∈ s := by simpa [closeIterConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'

theorem closeIter_trace_step (seed limit s i : M)
    (h : (closeIterConstruction (M := M)).CSeq ![seed] s)
    (hl : limit + 1 = lh s) (hi : i < limit) :
    znth s (i + 1) = closeOne (znth s i) := by
  have hlt : i < lh s := by rw [← hl]; exact lt_trans hi (by simp)
  have hm := h.succ i (by simp [← hl, hi]) (znth s i) (h.seq.znth hlt)
  have hm' : ⟪i + 1, closeOne (znth s i)⟫ ∈ s := by simpa [closeIterConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'

theorem closeIter_trace_scoped (seed limit s i : M)
    (h : (closeIterConstruction (M := M)).CSeq ![seed] s)
    (hl : limit + 1 = lh s) (hs : IsSemiformula SourceL 0 seed)
    (hi : i ≤ limit) : IsSemiformula SourceL 0 (znth s i) := by
  have hdef : 𝚺₁-Predicate (fun j : M => j ≤ limit → IsSemiformula SourceL 0 (znth s j)) := by
    definability
  have hall : ∀ j : M, j ≤ limit → IsSemiformula SourceL 0 (znth s j) := by
    intro j
    induction j using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero =>
      intro _
      rw [closeIter_trace_start seed s h]
      exact hs
    case succ j ih =>
      intro hj
      have hjlt : j < limit := lt_iff_succ_le.mpr hj
      rw [closeIter_trace_step seed limit s j h hl hjlt]
      exact closeOne_scoped _ (ih (le_of_lt hjlt))
  exact hall i hi

#print axioms closeIter_trace_scoped
#print axioms closeIter_trace_start
#print axioms closeIter_trace_step
#print axioms closeIter_exists_trace
end models
end PA194BindSource
