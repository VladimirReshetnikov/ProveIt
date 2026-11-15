import PA194ModelPartialAdmission
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
local instance rankedEnvironmentZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance rankedEnvironmentOne : One M := ⟨F oneCode Fin.elim0⟩
local instance rankedEnvironmentAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance rankedEnvironmentMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance rankedEnvironmentLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance rankedEnvironmentIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The free stack records descending prior labels. Empty tails decode to zero. -/
def RankedEnvironment (e : M) : Prop :=
  len (simFree e)+1 ≤ simBase e ∧
    ∀ i < len (simFree e), (simFree e).[i]+(i+1) ≤ simBase e

theorem rankedEnvironment_definable : 𝚷₁-Predicate (RankedEnvironment : M → Prop) := by
  unfold RankedEnvironment simFree simBase
  definability

theorem rankedEnvironment_push (e : M) (h : RankedEnvironment e) :
    RankedEnvironment (simPushFree e) := by
  unfold RankedEnvironment at h ⊢
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
      have h1 := add_le_add_right hj' (1 : M)
      simp only [nth_adjoin_succ]
      simpa only [add_assoc,add_comm,add_left_comm] using h1

theorem rankedEnvironment_unpush (e : M) (h : RankedEnvironment (simPushFree e)) :
    RankedEnvironment e := by
  unfold RankedEnvironment at h ⊢
  obtain ⟨_,hfree,hbase,_⟩ := simPushFree_fields e
  rw [hfree,hbase] at h
  simp only [←adjoin_def,len_adjoin] at h
  constructor
  · have h1 : (len (simFree e)+1)+1 ≤ simBase e+1 := by
      simpa only [add_assoc] using h.1
    exact (add_le_add_iff_right 1).mp h1
  · intro i hi
    have hi' : i+1 < len (simFree e)+1 := by
      simpa only [add_comm] using add_lt_add_right hi 1
    have h1 := h.2 (i+1) hi'
    simp only [nth_adjoin_succ] at h1
    have h2 : ((simFree e).[i]+(i+1))+1 ≤ simBase e+1 := by
      simpa only [add_assoc] using h1
    exact (add_le_add_iff_right 1).mp h2

theorem rankedEnvironment_free_lt (e i : M) (h : RankedEnvironment e) :
    (simFree e).[i] < simBase e := by
  by_cases hi : i < len (simFree e)
  · have h1 : (1 : M) ≤ i+1 := by
      have hz : (0 : M) ≤ i := zero_le
      simpa only [zero_add,add_comm] using add_le_add_right hz 1
    have h2 : (simFree e).[i]+1 ≤ (simFree e).[i]+(i+1) := by
      have hh := add_le_add_right h1 ((simFree e).[i])
      simpa only [add_comm] using hh
    exact lt_of_lt_of_le (lt_add_one _) (le_trans h2 (h.2 i hi))
  · rw [nth_lt_len (le_of_not_gt hi)]
    have hpos : (0 : M) < len (simFree e)+1 := by simp
    exact lt_of_lt_of_le hpos h.1

theorem rankedEnvironment_initial (bound d : M) :
    RankedEnvironment (partialInitialEnvironment bound d) := by
  unfold RankedEnvironment partialInitialEnvironment simFree simBase
  simp

/-- Stronger partial admission with a push/pop-stable ranked free stack. -/
def RankedAdmission (e d : M) : Prop :=
  RankedEnvironment e ∧ simBase e+(d+1) ≤ simReserve e

theorem rankedAdmission_definable : 𝚷₁-Relation (RankedAdmission : M → M → Prop) := by
  haveI : 𝚷₁-Predicate (RankedEnvironment : M → Prop) := rankedEnvironment_definable
  unfold RankedAdmission simBase simReserve
  definability

theorem rankedAdmission_to_partial (B e d : M) (h : RankedAdmission e d) :
    PartialAdmission B e d := ⟨fun i _ => rankedEnvironment_free_lt e i h.1,h.2⟩

theorem rankedAdmission_initial (bound d : M) :
    RankedAdmission (partialInitialEnvironment bound d) d :=
  ⟨rankedEnvironment_initial bound d,(partialAdmission_initial 0 bound d).2⟩

theorem rankedAdmission_child (e d child : M) (hc : child < d)
    (h : RankedAdmission e d) : RankedAdmission e child :=
  ⟨h.1,(partialAdmission_child 0 e d child hc (rankedAdmission_to_partial 0 e d h)).2⟩

theorem rankedAdmission_push_child (e d child : M) (hc : child < d)
    (h : RankedAdmission e d) : RankedAdmission (simPushFree e) child :=
  ⟨rankedEnvironment_push e h.1,
    (partialAdmission_push_child 0 e d child hc (rankedAdmission_to_partial 0 e d h)).2⟩

theorem rankedAdmission_pop_push_child (e d child : M) (hc : child < d)
    (h : RankedAdmission (simPushFree e) d) :
    RankedAdmission (simPopFree (simPushFree e)) child := by
  rw [simPopFree_push]
  refine ⟨rankedEnvironment_unpush e h.1,?_⟩
  obtain ⟨_,_,hbase,hreserve⟩ := simPushFree_fields e
  have hslack := h.2
  rw [hbase,hreserve] at hslack
  have hcd : child+1 ≤ d+1 := by
    have hh := add_le_add_right (le_of_lt hc) (1 : M)
    simpa only [add_comm] using hh
  have h1 : simBase e+(child+1) ≤ simBase e+(d+1) := by
    have hh := add_le_add_right hcd (simBase e)
    simpa only [add_comm] using hh
  have h2 : simBase e+(d+1) ≤ (simBase e+1)+(d+1) := by
    have hh := add_le_add_right (le_of_lt (lt_add_one (simBase e))) (d+1)
    simpa only [add_comm] using hh
  exact le_trans h1 (le_trans h2 hslack)

theorem rankedAdmission_axiomReserve (e s p : M)
    (h : RankedAdmission e (axm s p)) : simBase e+p ≤ simReserve e :=
  partialAdmission_axiomReserve 0 e s p (rankedAdmission_to_partial 0 e _ h)

theorem rankedAdmission_freshPositiveAtom (e s d r a b : M)
    (h : RankedAdmission e d) (hs : IsFormulaSet SourceL s)
    (hq : (^rel (2 : M) r ?[a,b]) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^rel (2 : M) r ?[a,b]))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^rel (2 : M) r ?[a,b])))) := by
  have hp := rankedAdmission_to_partial s e d h
  exact simRuleAllFresh_closedPositiveAtom e s r a b hs hq hp.1
    (ne_of_lt (partialAdmission_base_lt_reserve s e d hp))

theorem rankedAdmission_freshNegativeAtom (e s d r a b : M)
    (h : RankedAdmission e d) (hs : IsFormulaSet SourceL s)
    (hq : (^nrel (2 : M) r ?[a,b]) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^nrel (2 : M) r ?[a,b]))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^nrel (2 : M) r ?[a,b])))) := by
  have hp := rankedAdmission_to_partial s e d h
  exact simRuleAllFresh_closedNegativeAtom e s r a b hs hq hp.1
    (ne_of_lt (partialAdmission_base_lt_reserve s e d hp))

#print axioms rankedAdmission_definable
#print axioms rankedAdmission_to_partial
#print axioms rankedAdmission_initial
#print axioms rankedAdmission_child
#print axioms rankedAdmission_push_child
#print axioms rankedAdmission_pop_push_child
#print axioms rankedAdmission_axiomReserve
#print axioms rankedAdmission_freshPositiveAtom
#print axioms rankedAdmission_freshNegativeAtom
#print axioms rankedEnvironment_definable
#print axioms rankedEnvironment_push
#print axioms rankedEnvironment_unpush
#print axioms rankedEnvironment_free_lt
#print axioms rankedEnvironment_initial
end models
end PA194ModelLogic
