import PA194ModelFreshAtom
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
local instance pushInvariantZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance pushInvariantOne : One M := ⟨F oneCode Fin.elim0⟩
local instance pushInvariantAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance pushInvariantMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance pushInvariantLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance pushInvariantIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The bounded free-stack freshness invariant is preserved when the current
base label is pushed and the base advances, even for nonstandard indices. -/
theorem simPushFree_stackBound (e B : M)
    (h : ∀ i < B, (simFree e).[i] < simBase e) :
    ∀ i < B, (simFree (simPushFree e)).[i] < simBase (simPushFree e) := by
  intro i hi
  obtain ⟨_,hfree,hbase,_⟩ := simPushFree_fields e
  rw [hfree,hbase]
  rcases zero_or_succ i with (rfl | ⟨j,rfl⟩)
  · simpa only [←adjoin_def,nth_adjoin_zero] using lt_add_one (simBase e)
  · have hj : j < B := lt_trans (lt_add_one j) hi
    have hj' := h j hj
    have hlt := lt_trans hj' (lt_add_one (simBase e))
    simpa only [←adjoin_def,nth_adjoin_succ] using hlt

/-- Reserve slack decreases by one when the eigenvariable environment is pushed. -/
theorem simPushFree_reserveSlack (e d : M)
    (h : simBase e + (d+1) ≤ simReserve e) :
    simBase (simPushFree e) + d ≤ simReserve (simPushFree e) := by
  obtain ⟨_,_,hbase,hreserve⟩ := simPushFree_fields e
  rw [hbase,hreserve]
  have he : (simBase e+1)+d = simBase e+(d+1) := by ac_rfl
  rw [he]
  exact h

/-- Reconstruct the previous free-variable environment by dropping the head
of the free stack and decrementing the base. -/
noncomputable def simPopFree (e : M) : M :=
  pair (simBound e) (pair (π₂ (F predCode ![simFree e]))
    (pair (F predCode ![simBase e]) (simReserve e)))

theorem simPopFree_push (e : M) : simPopFree (simPushFree e) = e := by
  obtain ⟨hbound,hfree,hbase,hreserve⟩ := simPushFree_fields e
  unfold simPopFree
  rw [hbound,hfree,hbase,hreserve]
  have hp : F predCode ![pair (simBase e) (simFree e)+1] = pair (simBase e) (simFree e) := by
    have hv : (![pair (simBase e) (simFree e)+1] : Fin 1 → M) = (fun _ => pair (simBase e) (simFree e)+1) := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]
    exact modelPredAddOne _
  have hb : F predCode ![simBase e+1] = simBase e := by
    have hv : (![simBase e+1] : Fin 1 → M) = (fun _ => simBase e+1) := by
      funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [hv]
    exact modelPredAddOne _
  rw [hp,hb,pi₂_pair]
  simp [simBound,simFree,simBase,simReserve,pair_unpair]

/-- Shift-rule target implication on a pushed environment, once the exact
source-shift translation bridge is known for the formula. -/
theorem simRuleShift_of_bridge (e p : M)
    (h : ShiftBridge p (simBound e) (simFree e) (simBase e) (simReserve e)) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr (simPushFree e) (shift SourceL p))
      (numericalTranslation.tr (simPopFree (simPushFree e)) p)) := by
  rw [simPopFree_push]
  change TargetProvable (impValue (negatedTranslation (simPushFree e) (shift SourceL p))
    (negatedTranslation e p))
  obtain ⟨hbound,hfree,hbase,hreserve⟩ := simPushFree_fields e
  rw [negatedTranslation_any,negatedTranslation_any,hbound,hfree,hbase,hreserve]
  unfold ShiftBridge at h
  rw [h]
  exact imp_refl _

theorem simRuleShift_positiveAtom (e r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr (simPushFree e) (shift SourceL (^rel (2 : M) r ?[a,b])))
      (numericalTranslation.tr (simPopFree (simPushFree e)) (^rel (2 : M) r ?[a,b]))) := by
  apply simRuleShift_of_bridge
  exact shift_positiveAtom_translation r a b (simBound e) (simFree e) (simBase e) (simReserve e) hr ha hb

theorem simRuleShift_negativeAtom (e r a b : M)
    (hr : SourceL.IsRel 2 r) (ha : IsUTerm SourceL a) (hb : IsUTerm SourceL b) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr (simPushFree e) (shift SourceL (^nrel (2 : M) r ?[a,b])))
      (numericalTranslation.tr (simPopFree (simPushFree e)) (^nrel (2 : M) r ?[a,b]))) := by
  apply simRuleShift_of_bridge
  exact shift_negativeAtom_translation r a b (simBound e) (simFree e) (simBase e) (simReserve e) hr ha hb

#print axioms simRuleShift_of_bridge
#print axioms simRuleShift_positiveAtom
#print axioms simRuleShift_negativeAtom
#print axioms simPopFree_push
#print axioms simPushFree_stackBound
#print axioms simPushFree_reserveSlack
end models
end PA194ModelLogic
