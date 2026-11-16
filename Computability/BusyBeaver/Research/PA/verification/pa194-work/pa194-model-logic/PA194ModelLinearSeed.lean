import PA194ModelLinearEnvironment
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
local instance linearSeedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance linearSeedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance linearSeedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance linearSeedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance linearSeedLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance linearSeedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


noncomputable def linearSeed (bound reserve n : M) : M :=
  pair bound (pair (F allocateBound ![n,1,0]) (pair (n+1) reserve))

theorem linearSeed_succ (bound reserve n : M) :
    linearSeed bound reserve (n+1) = simPushFree (linearSeed bound reserve n) := by
  unfold linearSeed simPushFree simBound simFree simBase simReserve
  simp only [pi₁_pair,pi₂_pair,allocateBound_succ]
  congr 3
  ac_rfl

theorem linearSeedInvariant_definable (stage : M → M) (hs : 𝚺₁-Function₁ stage) :
    𝚺₁-Predicate (fun k : M =>
      (len (stage k)+1 ≤ k+1 ∧ ∀ i < len (stage k), (stage k).[i]+(i+1)=k+1) ∧
      len (stage k)=k) := by
  haveI := hs
  definability

theorem linearSeed_properties (bound reserve n : M) :
    LinearEnvironment (linearSeed bound reserve n) ∧ len (simFree (linearSeed bound reserve n)) = n := by
  let stage : M → M := fun k => F allocateBound ![k,1,0]
  have hp' := linearSeedInvariant_definable stage (PA194CodeInstance.unary_of_three allocateBound 1 0)
  have hp : 𝚺₁-Predicate (fun k : M =>
      LinearEnvironment (linearSeed bound reserve k) ∧ len (simFree (linearSeed bound reserve k)) = k) := by
    simpa only [LinearEnvironment,linearSeed,simFree,simBase,pi₁_pair,pi₂_pair] using hp'
  induction n using ISigma1.sigma1_succ_induction
  · exact hp
  case zero =>
    constructor
    · unfold LinearEnvironment linearSeed simFree simBase
      simp [allocateBound_zero]
    · simp [linearSeed,simFree,allocateBound_zero]
  case succ n ih =>
    rw [linearSeed_succ]
    constructor
    · exact linearEnvironment_push _ ih.1
    · obtain ⟨_,hf,_,_⟩ := simPushFree_fields (linearSeed bound reserve n)
      rw [hf,←adjoin_def,len_adjoin,ih.2]

/-- An invariant with enough free labels for one pop per remaining code step. -/
def DepthAdmission (e d : M) : Prop :=
  LinearEnvironment e ∧ d+1 ≤ len (simFree e) ∧ simBase e+(d+1) ≤ simReserve e

theorem depthAdmission_definable : 𝚷₁-Relation (DepthAdmission : M → M → Prop) := by
  haveI : 𝚷₁-Predicate (LinearEnvironment : M → Prop) := linearEnvironment_definable
  unfold DepthAdmission simFree simBase simReserve
  definability

theorem depthAdmission_ranked (e d : M) (h : DepthAdmission e d) : RankedAdmission e d :=
  ⟨linearEnvironment_ranked e h.1,h.2.2⟩

theorem depthAdmission_initial (bound d : M) :
    DepthAdmission (linearSeed bound (((d+1)+1)+(d+1)) (d+1)) d := by
  have hp := linearSeed_properties bound (((d+1)+1)+(d+1)) (d+1)
  refine ⟨hp.1,?_,?_⟩
  · rw [hp.2]
  · simp [linearSeed,simBase,simReserve]

theorem depthAdmission_child (e d child : M) (hc : child < d)
    (h : DepthAdmission e d) : DepthAdmission e child := by
  refine ⟨h.1,?_,(rankedAdmission_child e d child hc (depthAdmission_ranked e d h)).2⟩
  have hh : child+1 ≤ d+1 := by simpa only [add_comm] using add_le_add_right (le_of_lt hc) (1 : M)
  exact le_trans hh h.2.1

theorem depthAdmission_push_child (e d child : M) (hc : child < d)
    (h : DepthAdmission e d) : DepthAdmission (simPushFree e) child := by
  refine ⟨linearEnvironment_push e h.1,?_,
    (rankedAdmission_push_child e d child hc (depthAdmission_ranked e d h)).2⟩
  obtain ⟨_,hf,_,_⟩ := simPushFree_fields e
  rw [hf,←adjoin_def,len_adjoin]
  have hh : child+1 ≤ d+1 := by simpa only [add_comm] using add_le_add_right (le_of_lt hc) (1 : M)
  exact le_trans (le_trans hh h.2.1) (le_of_lt (lt_add_one _))

theorem depthAdmission_nonempty (e d : M) (h : DepthAdmission e d) : simFree e ≠ 0 := by
  intro hz
  have hh := h.2.1
  rw [hz] at hh
  simp at hh

theorem depthAdmission_pop_child (e d child : M) (hc : child < d)
    (h : DepthAdmission e d) : DepthAdmission (simPopFree e) child := by
  have hn := depthAdmission_nonempty e d h
  have hi := simPushFree_pop_of_linear e h.1 hn
  have hr : RankedAdmission (simPopFree e) child := by
    have hh : RankedAdmission (simPushFree (simPopFree e)) d := by rw [hi]; exact depthAdmission_ranked e d h
    simpa only [simPopFree_push] using rankedAdmission_pop_push_child (simPopFree e) d child hc hh
  refine ⟨linearEnvironment_pop e h.1 hn,?_,hr.2⟩
  obtain ⟨_,hf,_,_⟩ := simPushFree_fields (simPopFree e)
  have hlen : len (simFree e) = len (simFree (simPopFree e))+1 := by
    calc
      len (simFree e) = len (simFree (simPushFree (simPopFree e))) := by rw [hi]
      _ = len (simFree (simPopFree e))+1 := by rw [hf,←adjoin_def,len_adjoin]
  have hd : d ≤ len (simFree (simPopFree e)) := by
    apply (add_le_add_iff_right 1).mp
    simpa only [hlen] using h.2.1
  exact le_trans (succ_le_iff_lt.mpr hc) hd

#print axioms linearSeed_succ
#print axioms linearSeed_properties
#print axioms depthAdmission_definable
#print axioms depthAdmission_initial
#print axioms depthAdmission_child
#print axioms depthAdmission_push_child
#print axioms depthAdmission_nonempty
#print axioms depthAdmission_pop_child
end models
end PA194ModelLogic
