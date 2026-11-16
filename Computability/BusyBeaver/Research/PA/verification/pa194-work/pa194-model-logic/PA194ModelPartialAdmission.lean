import PA194ModelPushInvariants
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
local instance partialAdmissionZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance partialAdmissionOne : One M := ⟨F oneCode Fin.elim0⟩
local instance partialAdmissionAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance partialAdmissionMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance partialAdmissionLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance partialAdmissionIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguagePartialAdmissionEq : Language.Eq SourceL := ⟨M6.PA.RelationalSource.Relation.eq⟩

/-- A candidate partial invariant: free labels below B are below the base,
and reserve slack dominates the code of the current derivation node. -/
def PartialAdmission (B e d : M) : Prop :=
  (∀ i < B, (simFree e).[i] < simBase e) ∧ simBase e + (d+1) ≤ simReserve e

theorem partialAdmission_definable (B : M) : 𝚷₁-Relation (PartialAdmission B) := by
  unfold PartialAdmission simFree simBase simReserve
  definability

theorem partialAdmission_child (B e d child : M) (hc : child < d)
    (h : PartialAdmission B e d) : PartialAdmission B e child := by
  refine ⟨h.1,?_⟩
  have hcd : child+1 ≤ d+1 := by
    have hh := add_le_add_right (le_of_lt hc) (1 : M)
    simpa only [add_comm] using hh
  have hbase : simBase e + (child+1) ≤ simBase e + (d+1) := by
    have hh := add_le_add_right hcd (simBase e)
    simpa only [add_comm] using hh
  exact le_trans hbase h.2

theorem partialAdmission_push_child (B e d child : M) (hc : child < d)
    (h : PartialAdmission B e d) : PartialAdmission B (simPushFree e) child := by
  refine ⟨simPushFree_stackBound e B h.1,?_⟩
  obtain ⟨_,_,hbase,hreserve⟩ := simPushFree_fields e
  rw [hbase,hreserve]
  have hcd : child+1 ≤ d := succ_le_iff_lt.mpr hc
  have hcd1 : (child+1)+1 ≤ d+1 := by
    have hh := add_le_add_right hcd (1 : M)
    simpa only [add_comm] using hh
  have hbase : simBase e + ((child+1)+1) ≤ simBase e + (d+1) := by
    have hh := add_le_add_right hcd1 (simBase e)
    simpa only [add_comm] using hh
  have he : (simBase e+1)+(child+1) = simBase e+((child+1)+1) := by ac_rfl
  rw [he]
  exact le_trans hbase h.2

/-- The source set at any node is bounded by an ambient bound on its code. -/
theorem derivationSourceSet_le (B d : M) (hd : d ≤ B) : fstIdx d ≤ B :=
  le_trans (fstIdx_le_self d) hd

theorem partialAdmission_and (B e s p q d₁ d₂ : M)
    (h : PartialAdmission B e (andIntro s p q d₁ d₂)) :
    PartialAdmission B e d₁ ∧ PartialAdmission B e d₂ :=
  ⟨partialAdmission_child B e _ _ (dp_lt_andIntro s p q d₁ d₂) h,
   partialAdmission_child B e _ _ (dq_lt_andIntro s p q d₁ d₂) h⟩

theorem partialAdmission_or (B e s p q d : M)
    (h : PartialAdmission B e (orIntro s p q d)) : PartialAdmission B e d :=
  partialAdmission_child B e _ _ (d_lt_orIntro s p q d) h

theorem partialAdmission_all (B e s p d : M)
    (h : PartialAdmission B e (allIntro s p d)) : PartialAdmission B (simPushFree e) d :=
  partialAdmission_push_child B e _ _ (s_lt_allIntro s p d) h

theorem partialAdmission_ex (B e s p t d : M)
    (h : PartialAdmission B e (exsIntro s p t d)) : PartialAdmission B e d :=
  partialAdmission_child B e _ _ (d_lt_exsIntro s p t d) h

theorem partialAdmission_weakening (B e s d : M)
    (h : PartialAdmission B e (wkRule s d)) : PartialAdmission B e d :=
  partialAdmission_child B e _ _ (d_lt_wkRule s d) h

theorem partialAdmission_cut (B e s p d₁ d₂ : M)
    (h : PartialAdmission B e (cutRule s p d₁ d₂)) :
    PartialAdmission B e d₁ ∧ PartialAdmission B e d₂ :=
  ⟨partialAdmission_child B e _ _ (d₁_lt_cutRule s p d₁ d₂) h,
   partialAdmission_child B e _ _ (d₂_lt_cutRule s p d₁ d₂) h⟩

theorem partialAdmission_codeReserve (B e d p : M) (hp : p ≤ d+1)
    (h : PartialAdmission B e d) : simBase e+p ≤ simReserve e := by
  have hbase : simBase e+p ≤ simBase e+(d+1) := by
    have hh := add_le_add_right hp (simBase e)
    simpa only [add_comm] using hh
  exact le_trans hbase h.2

theorem partialAdmission_axiomReserve (B e s p : M)
    (h : PartialAdmission B e (axm s p)) : simBase e+p ≤ simReserve e := by
  apply partialAdmission_codeReserve B e (axm s p) p _ h
  exact le_trans (le_of_lt (p_lt_axm s p)) (le_of_lt (lt_add_one _))

theorem partialAdmission_base_lt_reserve (B e d : M) (h : PartialAdmission B e d) :
    simBase e < simReserve e := by
  have hd : (1 : M) ≤ d+1 := by
    have hz : (0 : M) ≤ d := zero_le
    simpa only [zero_add,add_comm] using add_le_add_right hz 1
  have hbase : simBase e+1 ≤ simBase e+(d+1) := by
    have hh := add_le_add_right hd (simBase e)
    simpa only [add_comm] using hh
  exact lt_of_lt_of_le (lt_add_one (simBase e)) (le_trans hbase h.2)

theorem partialAdmission_stackForSet (B e d s : M) (hs : s ≤ B) (h : PartialAdmission B e d) :
    ∀ i < s, (simFree e).[i] < simBase e := by
  intro i hi
  exact h.1 i (lt_of_lt_of_le hi hs)

theorem simRuleEqAxiom_partialAdmission (B e s p : M)
    (h : PartialAdmission B e (axm s p)) :
    letI := finiteEqTheoryDelta
    p ∈ (Theory.eqAxiom SourceL).Δ₁Class →
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1) := by
  letI := finiteEqTheoryDelta
  exact simRuleEqAxiom e p (partialAdmission_axiomReserve B e s p h)

theorem simRuleAllFresh_partialPositiveAtom (B e s p d r a b : M)
    (h : PartialAdmission B e (allIntro s p d)) (hB : allIntro s p d ≤ B)
    (hs : IsFormulaSet SourceL s) (hq : (^rel (2 : M) r ?[a,b]) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^rel (2 : M) r ?[a,b]))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^rel (2 : M) r ?[a,b])))) := by
  have hsB : s ≤ B := le_trans (le_of_lt (seq_lt_allIntro s p d)) hB
  exact simRuleAllFresh_closedPositiveAtom e s r a b hs hq
    (partialAdmission_stackForSet B e _ s hsB h)
    (ne_of_lt (partialAdmission_base_lt_reserve B e _ h))

theorem simRuleAllFresh_partialNegativeAtom (B e s p d r a b : M)
    (h : PartialAdmission B e (allIntro s p d)) (hB : allIntro s p d ≤ B)
    (hs : IsFormulaSet SourceL s) (hq : (^nrel (2 : M) r ?[a,b]) ∈ s) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^nrel (2 : M) r ?[a,b]))
      (numericalQuant.all (simBase e) (numericalTranslation.tr e (^nrel (2 : M) r ?[a,b])))) := by
  have hsB : s ≤ B := le_trans (le_of_lt (seq_lt_allIntro s p d)) hB
  exact simRuleAllFresh_closedNegativeAtom e s r a b hs hq
    (partialAdmission_stackForSet B e _ s hsB h)
    (ne_of_lt (partialAdmission_base_lt_reserve B e _ h))

/-- A model-uniform initial packed environment with an all-zero free stack,
base one, and exactly the required reserve slack. -/
noncomputable def partialInitialEnvironment (bound d : M) : M :=
  pair bound (pair 0 (pair 1 (1+(d+1))))

theorem partialAdmission_initial (B bound d : M) :
    PartialAdmission B (partialInitialEnvironment bound d) d := by
  unfold PartialAdmission partialInitialEnvironment simFree simBase simReserve
  simp only [pi₁_pair,pi₂_pair]
  constructor
  · intro i hi
    simp
  · exact le_refl _

#print axioms partialAdmission_initial
#print axioms simRuleEqAxiom_partialAdmission
#print axioms simRuleAllFresh_partialPositiveAtom
#print axioms simRuleAllFresh_partialNegativeAtom
#print axioms partialAdmission_and
#print axioms partialAdmission_or
#print axioms partialAdmission_all
#print axioms partialAdmission_ex
#print axioms partialAdmission_weakening
#print axioms partialAdmission_cut
#print axioms partialAdmission_axiomReserve
#print axioms partialAdmission_base_lt_reserve
#print axioms partialAdmission_stackForSet
#print axioms partialAdmission_definable
#print axioms partialAdmission_child
#print axioms partialAdmission_push_child
#print axioms derivationSourceSet_le
end models
end PA194ModelLogic
