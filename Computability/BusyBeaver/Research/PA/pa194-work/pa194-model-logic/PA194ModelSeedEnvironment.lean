import PA194ModelBoundedRange
import PA194ModelBinderAllocationShift
import PA194RelExtTypedTranslation

/-! Deep linear-stack seeds and a depth-indexed partial compiler admission. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4000
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
local instance seedEnvironmentZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance seedEnvironmentOne : One M := ⟨F oneCode Fin.elim0⟩
local instance seedEnvironmentAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance seedEnvironmentMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance seedEnvironmentLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance seedEnvironmentIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]




/-- The environment is the canonical consecutive-label seed at its own stack length. -/
def SeedEnvironment (e : M) : Prop :=
  e = linearSeed (simBound e) (simReserve e) (len (simFree e))

theorem seedEnvironmentStage_definable (stage : M → M) (hs : 𝚺₁-Function₁ stage) :
    𝚷₁-Predicate (fun e : M => e = pair (simBound e)
      (pair (stage (len (simFree e))) (pair (len (simFree e)+1) (simReserve e)))) := by
  haveI := hs
  unfold simBound simFree simReserve
  definability

theorem seedEnvironment_definable : 𝚷₁-Predicate (SeedEnvironment : M → Prop) := by
  let stage : M → M := fun n => F allocateBound ![n,1,0]
  have hp := seedEnvironmentStage_definable stage (PA194CodeInstance.unary_of_three allocateBound 1 0)
  change 𝚷₁-Predicate (fun e : M => e = pair (simBound e)
    (pair (stage (len (simFree e))) (pair (len (simFree e)+1) (simReserve e))))
  exact hp

theorem seedEnvironment_seed (bound reserve n : M) : SeedEnvironment (linearSeed bound reserve n) := by
  have hl := (linearSeed_properties bound reserve n).2
  unfold SeedEnvironment
  simp only [linearSeed,simBound,simReserve,pi₁_pair,pi₂_pair]
  change linearSeed bound reserve n = linearSeed bound reserve (len (simFree (linearSeed bound reserve n)))
  rw [hl]

theorem seedEnvironment_linear (e : M) (h : SeedEnvironment e) : LinearEnvironment e := by
  rw [h]
  exact (linearSeed_properties _ _ _).1

theorem seedEnvironment_push (e : M) (h : SeedEnvironment e) : SeedEnvironment (simPushFree e) := by
  have he : simPushFree e = linearSeed (simBound e) (simReserve e) (len (simFree e)+1) := by
    calc
      simPushFree e = simPushFree (linearSeed (simBound e) (simReserve e) (len (simFree e))) := congrArg simPushFree h
      _ = _ := (linearSeed_succ _ _ _).symm
  rw [he]
  exact seedEnvironment_seed _ _ _

theorem seedEnvironment_pop (e d : M) (h : SeedEnvironment e) (hd : DepthAdmission e d) :
    SeedEnvironment (simPopFree e) := by
  have hn : (0 : M) < len (simFree e) := lt_of_lt_of_le (lt_of_le_of_lt zero_le (lt_add_one d)) hd.2.1
  rcases zero_or_succ (len (simFree e)) with hz | ⟨n, hn'⟩
  · rw [hz] at hn; exact False.elim ((not_lt_of_ge (le_refl (0 : M))) hn)
  · have he : e = simPushFree (linearSeed (simBound e) (simReserve e) n) := by
      calc
        e = linearSeed (simBound e) (simReserve e) (len (simFree e)) := h
        _ = linearSeed (simBound e) (simReserve e) (n+1) := by rw [hn']
        _ = _ := linearSeed_succ _ _ _
    rw [he,simPopFree_push]
    exact seedEnvironment_seed _ _ _

def SeedAdmission (bound reserve e d : M) : Prop :=
  DepthAdmission e d ∧ SeedEnvironment e ∧ simBound e = bound ∧ simReserve e = reserve

theorem seedAdmission_definable (bound reserve : M) :
    𝚷₁-Relation (SeedAdmission bound reserve : M → M → Prop) := by
  haveI : 𝚷₁-Relation (DepthAdmission : M → M → Prop) := depthAdmission_definable
  haveI : 𝚷₁-Predicate (SeedEnvironment : M → Prop) := seedEnvironment_definable
  unfold SeedAdmission simBound simReserve
  definability

theorem seedAdmission_initial (bound d : M) :
    SeedAdmission bound (((d+1)+1)+(d+1))
      (linearSeed bound (((d+1)+1)+(d+1)) (d+1)) d := by
  refine ⟨depthAdmission_initial bound d,seedEnvironment_seed _ _ _,?_,?_⟩
  · simp [linearSeed,simBound]
  · simp [linearSeed,simReserve]

theorem seedAdmission_child (bound reserve e d child : M) (hc : child < d)
    (h : SeedAdmission bound reserve e d) : SeedAdmission bound reserve e child :=
  ⟨depthAdmission_child e d child hc h.1,h.2⟩

theorem seedAdmission_push_child (bound reserve e d child : M) (hc : child < d)
    (h : SeedAdmission bound reserve e d) : SeedAdmission bound reserve (simPushFree e) child := by
  obtain ⟨hb,_,_,hr⟩ := simPushFree_fields e
  exact ⟨depthAdmission_push_child e d child hc h.1,seedEnvironment_push e h.2.1,
    hb.trans h.2.2.1,hr.trans h.2.2.2⟩

theorem seedAdmission_pop_child (bound reserve e d child : M) (hc : child < d)
    (h : SeedAdmission bound reserve e d) : SeedAdmission bound reserve (simPopFree e) child := by
  have hb : simBound (simPopFree e) = simBound e := by simp [simPopFree,simBound]
  have hr : simReserve (simPopFree e) = simReserve e := by simp [simPopFree,simReserve]
  exact ⟨depthAdmission_pop_child e d child hc h.1,seedEnvironment_pop e d h.2.1 h.1,
    hb.trans h.2.2.1,hr.trans h.2.2.2⟩

theorem seedAdmission_uniformBound (bound reserve : M) :
    ∃ B : M, ∀ e d : M, SeedAdmission bound reserve e d → e ≤ B := by
  obtain ⟨B,hB⟩ := linearSeed_boundedRange bound reserve reserve
  refine ⟨B,?_⟩
  intro e d h
  have hlen : len (simFree e) ≤ reserve := by
    have h1 : len (simFree e) ≤ simBase e :=
      le_trans (le_of_lt (lt_add_one _)) h.1.1.1
    have h2 : simBase e ≤ simReserve e := by
      have h3 : simBase e ≤ simBase e+(d+1) := by
        have hh := add_le_add_right (zero_le : (0 : M) ≤ d+1) (simBase e)
        simpa only [zero_add,add_zero,add_comm] using hh
      exact le_trans h3 h.1.2.2
    rw [h.2.2.2] at h2
    exact le_trans h1 h2
  have he := h.2.1
  change e = linearSeed (simBound e) (simReserve e) (len (simFree e)) at he
  rw [h.2.2.1,h.2.2.2] at he
  rw [he]
  exact hB _ hlen

#print axioms seedEnvironment_definable
#print axioms seedEnvironment_seed
#print axioms seedEnvironment_linear
#print axioms seedEnvironment_push
#print axioms seedEnvironment_pop
#print axioms seedAdmission_definable
#print axioms seedAdmission_initial
#print axioms seedAdmission_child
#print axioms seedAdmission_push_child
#print axioms seedAdmission_pop_child
#print axioms seedAdmission_uniformBound
end models
end PA194ModelLogic
