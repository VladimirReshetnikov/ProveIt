import PA194RankedOpenSeparation
import PA194ModelSeedEnvironment
import PA194ModelNumericalSeedRefutation

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
local instance closedSepClassifierZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance closedSepClassifierOne : One M := ⟨F oneCode Fin.elim0⟩
local instance closedSepClassifierAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance closedSepClassifierMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance closedSepClassifierLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance closedSepClassifierIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem closedSepAnd_left_le (a b : M) : a ≤ a ^⋏ b := by
  change a ≤ pair (4 : M) (pair a b)+1
  exact le_trans (le_trans (le_pair_left a b) (le_pair_right (4 : M) (pair a b))) (le_of_lt (lt_add_one _))

theorem closedSepAnd_right_le (a b : M) : b ≤ a ^⋏ b := by
  change b ≤ pair (4 : M) (pair a b)+1
  exact le_trans (le_trans (le_pair_right a b) (le_pair_right (4 : M) (pair a b))) (le_of_lt (lt_add_one _))

theorem closedSepOr_right_le (a b : M) : b ≤ a ^⋎ b := by
  change b ≤ pair (5 : M) (pair a b)+1
  exact le_trans (le_trans (le_pair_right a b) (le_pair_right (5 : M) (pair a b))) (le_of_lt (lt_add_one _))

theorem closedSepAll_body_le (p : M) : p ≤ ^∀ p := by
  change p ≤ pair (6 : M) p+1
  exact le_trans (le_pair_right (6 : M) p) (le_of_lt (lt_add_one _))

theorem closedSepEx_body_le (p : M) : p ≤ ^∃ p := by
  change p ≤ pair (7 : M) p+1
  exact le_trans (le_pair_right (7 : M) p) (le_of_lt (lt_add_one _))

theorem sepRoot_arg_le (p : M) : p ≤ sepRoot p := by
  let a : M := ^nrel (2 : M) (1 : M) (relExtVector 0 1)
  let b : M := ^rel (2 : M) (1 : M) (relExtVector 0 2)
  let c : M := ((^nrel (2 : M) (1 : M) (relExtVector 0 2)) ^⋎ neg SourceL p) ^⋎
    (^rel (2 : M) (1 : M) (relExtVector 0 1))
  have hinner : p ≤ sepInner p := by
    change p ≤ (a ^⋎ (b ^⋏ p)) ^⋏ c
    exact le_trans (closedSepAnd_right_le b p)
      (le_trans (closedSepOr_right_le a (b ^⋏ p)) (closedSepAnd_left_le (a ^⋎ (b ^⋏ p)) c))
  exact le_trans hinner (le_trans (closedSepAll_body_le (sepInner p))
    (le_trans (closedSepEx_body_le (^∀ (sepInner p))) (closedSepAll_body_le (^∃ (^∀ (sepInner p))))))

noncomputable def closedSepCode (q : M) : Prop :=
  ∃ p ≤ q, (IsSemiformula SourceL 1 p ∧ shift SourceL p = p) ∧ sepRoot p = q

theorem closedSepCode_sigma : 𝚺₁-Predicate (closedSepCode : M → Prop) := by
  unfold closedSepCode sepRoot sepInner
  definability

theorem closedSepCode_pi : 𝚷₁-Predicate (closedSepCode : M → Prop) := by
  unfold closedSepCode sepRoot sepInner
  definability

theorem closedSepCode_root (p : M) (hp : IsSemiformula SourceL 1 p)
    (hfree : shift SourceL p = p) : closedSepCode (sepRoot p) :=
  ⟨p,sepRoot_arg_le p,⟨hp,hfree⟩,rfl⟩

/-- The shift-invariant separation code predicate supplies the compiler's axiom leaf. -/
theorem closedSepCode_axiom_seed (reserve e s q : M)
    (ha : SeedAdmission 0 reserve e (axm s q)) (hq : closedSepCode q) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q) 1) := by
  obtain ⟨p,_,⟨hp,_⟩,heq⟩ := hq
  subst q
  exact simRuleSeparation_rankedAxiom e s p hp (depthAdmission_ranked e _ ha.1)

/-- An explicit model-level class inclusion supplies every axiom of an arbitrary
Δ₁ source theory from adjunctive axioms or shift-invariant separation roots. -/
theorem closedSepClassification_axiom_seed (T : Theory SourceL) [T.Δ₁]
    (reserve e s q : M) (ha : SeedAdmission 0 reserve e (axm s q))
    (hclass : letI := adjunctiveTheoryDelta
      ∀ p : M, p ∈ T.Δ₁Class → p ∈ adjunctiveTheory.Δ₁Class ∨ closedSepCode p)
    (hq : q ∈ T.Δ₁Class) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q) 1) := by
  letI := adjunctiveTheoryDelta
  rcases hclass q hq with hfixed | hsep
  · exact simRuleAdjunctiveAxiom_seed 0 reserve e s q ha hfixed
  · exact closedSepCode_axiom_seed reserve e s q ha hsep

/-- Conditional refutation transport for any source theory whose internal
axiom class is included in the explicitly classified candidates. -/
theorem closedSepClassification_refutation_target (T : Theory SourceL) [T.Δ₁] (d : M)
    (hclass : letI := adjunctiveTheoryDelta
      ∀ p : M, p ∈ T.Δ₁Class → p ∈ adjunctiveTheory.Δ₁Class ∨ closedSepCode p)
    (hd : Proof T d (^⊥ : M)) : TargetProvable (1 : M) := by
  apply numericalSeed_refutation_target T d hd
  intro reserve e s q ha hq
  exact closedSepClassification_axiom_seed T reserve e s q ha hclass hq

#print axioms closedSepClassification_axiom_seed
#print axioms closedSepClassification_refutation_target
#print axioms closedSepCode_axiom_seed
#print axioms sepRoot_arg_le
#print axioms closedSepCode_root
#print axioms closedSepCode_sigma
#print axioms closedSepCode_pi
end models
end PA194ModelLogic
