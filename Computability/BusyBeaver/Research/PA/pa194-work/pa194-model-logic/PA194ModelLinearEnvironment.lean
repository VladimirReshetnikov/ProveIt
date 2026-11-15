import PA194ModelRankedEnvironment
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
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
local instance linearEnvironmentZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance linearEnvironmentOne : One M := ⟨F oneCode Fin.elim0⟩
local instance linearEnvironmentAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance linearEnvironmentMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance linearEnvironmentLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance linearEnvironmentIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A stack of consecutive prior labels, with a strictly positive bottom base. -/
def LinearEnvironment (e : M) : Prop :=
  len (simFree e)+1 ≤ simBase e ∧
    ∀ i < len (simFree e), (simFree e).[i]+(i+1) = simBase e

theorem linearEnvironment_definable : 𝚷₁-Predicate (LinearEnvironment : M → Prop) := by
  unfold LinearEnvironment simFree simBase
  definability

theorem linearEnvironment_ranked (e : M) (h : LinearEnvironment e) : RankedEnvironment e := by
  refine ⟨h.1,?_⟩
  intro i hi
  rw [h.2 i hi]

theorem linearEnvironment_initial (bound d : M) :
    LinearEnvironment (partialInitialEnvironment bound d) := by
  unfold LinearEnvironment partialInitialEnvironment simFree simBase
  simp

theorem linearEnvironment_push (e : M) (h : LinearEnvironment e) :
    LinearEnvironment (simPushFree e) := by
  unfold LinearEnvironment at h ⊢
  obtain ⟨_,hfree,hbase,_⟩ := simPushFree_fields e
  rw [hfree,hbase]
  simp only [←adjoin_def,len_adjoin]
  constructor
  · have h1 := add_le_add_right h.1 (1 : M)
    simpa only [add_assoc,add_comm,add_left_comm] using h1
  · intro i hi
    rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
    · simp
    · have hj : j < len (simFree e) := by simpa using hi
      have hj' := h.2 j hj
      simp only [nth_adjoin_succ]
      rw [show (simFree e).[j]+(j+1+1) = ((simFree e).[j]+(j+1))+1 by ac_rfl,hj']

theorem linearEnvironment_unpush (e : M) (h : LinearEnvironment (simPushFree e)) :
    LinearEnvironment e := by
  unfold LinearEnvironment at h ⊢
  obtain ⟨_,hfree,hbase,_⟩ := simPushFree_fields e
  rw [hfree,hbase] at h
  simp only [←adjoin_def,len_adjoin] at h
  constructor
  · have h1 : (len (simFree e)+1)+1 ≤ simBase e+1 := by simpa only [add_assoc] using h.1
    exact (add_le_add_iff_right 1).mp h1
  · intro i hi
    have hi' : i+1 < len (simFree e)+1 := by simpa only [add_comm] using add_lt_add_right hi 1
    have h1 := h.2 (i+1) hi'
    simp only [nth_adjoin_succ] at h1
    have h2 : ((simFree e).[i]+(i+1))+1 = simBase e+1 := by simpa only [add_assoc] using h1
    exact add_right_cancel h2

theorem simPushFree_pop_of_linear (e : M) (h : LinearEnvironment e) (hn : simFree e ≠ 0) :
    simPushFree (simPopFree e) = e := by
  rcases nil_or_adjoin (simFree e) with hz | ⟨head,tail,hf⟩
  · exact False.elim (hn hz)
  have hzero : (0 : M) < len (simFree e) := by rw [hf]; simp
  have hhead := h.2 0 hzero
  rw [hf,nth_adjoin_zero] at hhead
  have hb : simBase e = head+1 := by simpa only [zero_add] using hhead.symm
  have hp : F predCode ![simFree e] = pair head tail := by
    rw [hf,adjoin_def]
    have hv : (![pair head tail+1] : Fin 1 → M) = (fun _ => pair head tail+1) := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]; exact modelPredAddOne _
  have hpb : F predCode ![simBase e] = head := by
    rw [hb]
    have hv : (![head+1] : Fin 1 → M) = (fun _ => head+1) := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]; exact modelPredAddOne _
  have hbnd : simBound (simPopFree e) = simBound e := by simp [simPopFree,simBound]
  have hfre : simFree (simPopFree e) = π₂ (F predCode ![simFree e]) := by simp [simPopFree,simFree]
  have hbas : simBase (simPopFree e) = F predCode ![simBase e] := by simp [simPopFree,simBase]
  have hres : simReserve (simPopFree e) = simReserve e := by simp [simPopFree,simReserve]
  unfold simPushFree
  rw [hbnd,hfre,hbas,hres,hp,hpb,pi₂_pair,←adjoin_def,←hf,←hb]
  simp [simBound,simFree,simBase,simReserve,pair_unpair]

/-- A nonempty consecutive stack can be popped while retaining the invariant. -/
theorem linearEnvironment_pop (e : M) (h : LinearEnvironment e) (hn : simFree e ≠ 0) :
    LinearEnvironment (simPopFree e) := by
  apply linearEnvironment_unpush
  rw [simPushFree_pop_of_linear e h hn]
  exact h

/-- A nonempty consecutive stack is exactly in the push image. -/
theorem linearEnvironment_pushImage (e : M) (h : LinearEnvironment e) (hn : simFree e ≠ 0) :
    ∃ e', simPushFree e' = e := ⟨simPopFree e, simPushFree_pop_of_linear e h hn⟩

#print axioms linearEnvironment_definable
#print axioms linearEnvironment_ranked
#print axioms linearEnvironment_initial
#print axioms linearEnvironment_push
#print axioms linearEnvironment_unpush
#print axioms simPushFree_pop_of_linear
#print axioms linearEnvironment_pop
#print axioms linearEnvironment_pushImage
end models
end PA194ModelLogic
