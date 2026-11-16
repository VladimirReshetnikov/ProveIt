import PA194ModelSeparationAxiom
import PA194ModelRankedEnvironment
import PA194ModelSeedEnvironment
set_option autoImplicit false
set_option maxHeartbeats 5000000
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
local instance sepRankZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sepRankOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sepRankAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sepRankMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sepRankLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sepRankIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Open one-variable separation with arbitrary free parameters, using ranked
compiler environments; the explicit reserve inequality still needs to be
established for the particular axiom leaf. -/
theorem simRuleSeparation_ranked (e φ : M)
    (hφ : IsSemiformula SourceL 1 φ) (he : RankedEnvironment e)
    (hreserve : (simBase e+1)+1 < simReserve e) :
    TargetProvable (impValue (negatedTranslation e (sepRoot φ)) 1) := by
  apply simRuleSeparation e φ hφ
  · intro i hi
    exact ne_of_lt (lt_trans (rankedEnvironment_free_lt e i he) (lt_add_one (simBase e)))
  · exact ne_of_gt (lt_trans (lt_add_one (simBase e+1)) hreserve)
  · exact ne_of_gt hreserve
/-- Every separation instance has a positive outer universal constructor. -/
theorem sepRoot_exceeds_two (φ : M) : (1 : M)+1 < sepRoot φ := by
  change (1 : M)+1 < pair (6 : M) (^∃ (^∀ (sepInner φ))) + 1
  have h6 : (1 : M)+1 ≤ (6 : M) := by norm_num
  exact lt_of_le_of_lt (le_trans h6 (le_pair_left (6 : M) _)) (lt_add_one _)

/-- The axiom-node reserve bound supplies separation slack once the source
separation code is known to exceed two. -/
theorem simRuleSeparation_rankedAxiom (e s φ : M)
    (hφ : IsSemiformula SourceL 1 φ)
    (ha : RankedAdmission e (axm s (sepRoot φ)))
    :
    TargetProvable (impValue (negatedTranslation e (sepRoot φ)) 1) := by
  apply simRuleSeparation_ranked e φ hφ ha.1
  have h := add_lt_add_left (sepRoot_exceeds_two φ) (simBase e)
  have hb := rankedAdmission_axiomReserve e s (sepRoot φ) ha
  apply lt_of_lt_of_le _ hb
  simpa only [add_assoc,add_comm,add_left_comm] using h
/-- Seed admission supplies both rank and reserve at the actual axiom node. -/
theorem simRuleSeparation_seededAxiom (bound reserve e s φ : M)
    (hφ : IsSemiformula SourceL 1 φ)
    (ha : SeedAdmission bound reserve e (axm s (sepRoot φ))) :
    TargetProvable (impValue (negatedTranslation e (sepRoot φ)) 1) := by
  exact simRuleSeparation_rankedAxiom e s φ hφ (depthAdmission_ranked e _ ha.1)
#print axioms simRuleSeparation_seededAxiom
#print axioms sepRoot_exceeds_two
#print axioms simRuleSeparation_ranked
#print axioms simRuleSeparation_rankedAxiom
end models
end PA194ModelLogic
