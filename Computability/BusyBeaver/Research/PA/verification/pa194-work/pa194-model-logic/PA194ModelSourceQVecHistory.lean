import PA194ModelOneLevelFree
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
local instance sourceQVecHistoryZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceQVecHistoryOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceQVecHistoryAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceQVecHistoryMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceQVecHistoryLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceQVecHistoryIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Iteration of the actual relational-source qVec over model-internal depths. -/
def sourceQVecZeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out seed. out = seed”
noncomputable def sourceQVecSuccDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index seed. !(qVecGraph SourceL) out previous”
noncomputable def sourceQVecBlueprint : PR.Blueprint 1 where
  zero := sourceQVecZeroDef
  succ := sourceQVecSuccDef
noncomputable def sourceQVecConstruction : PR.Construction M sourceQVecBlueprint where
  zero p := p 0
  succ _ _ previous := qVec SourceL previous
  zero_defined := .mk fun e => by simp [sourceQVecBlueprint,sourceQVecZeroDef]
  succ_defined := .mk fun e => by simp [sourceQVecBlueprint,sourceQVecSuccDef]

theorem sourceQVec_exists_trace (seed limit : M) :
    ∃ s : M, (sourceQVecConstruction (M := M)).CSeq ![seed] s ∧ limit + 1 = lh s :=
  PR.Construction.CSeq.exists _ _ _

theorem sourceQVec_trace_start (seed s : M) (h : (sourceQVecConstruction (M := M)).CSeq ![seed] s) :
    znth s 0 = seed := by
  have hm := h.zero
  have hm' : ⟪(0 : M), seed⟫ ∈ s := by simpa [sourceQVecConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'

theorem sourceQVec_trace_step (seed limit s i : M)
    (h : (sourceQVecConstruction (M := M)).CSeq ![seed] s)
    (hl : limit + 1 = lh s) (hi : i < limit) :
    znth s (i + 1) = qVec SourceL (znth s i) := by
  have hlt : i < lh s := by rw [← hl]; exact lt_trans hi (by simp)
  have hm := h.succ i (by simp [← hl, hi]) (znth s i) (h.seq.znth hlt)
  have hm' : ⟪i + 1, qVec SourceL (znth s i)⟫ ∈ s := by simpa [sourceQVecConstruction] using hm
  exact h.seq.znth_eq_of_mem hm'

#print axioms sourceQVec_exists_trace
#print axioms sourceQVec_trace_start
#print axioms sourceQVec_trace_step
end models
end PA194ModelLogic
