import PA194RankedOpenSeparation
import PA194ModelSourceOpeningGeneral
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
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance sepRankClosedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sepRankClosedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sepRankClosedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sepRankClosedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sepRankClosedLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sepRankClosedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Admission at the closed axiom gives the pushed-environment freshness
and the small reserve slack needed for the open separation leaf. -/
theorem simRuleSeparation_closedOnce_ranked (bound reserve e s p φ : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∀ p) ∈ s)
    (hφ : IsSemiformula SourceL 1 φ)
    (hopen : LO.FirstOrder.Arithmetic.Bootstrapping.free SourceL p = sepRoot φ)
    (ha : SeedAdmission bound reserve e (axm s (^∀ p))) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (^∀ p)) 1) := by
  have har : RankedAdmission e (axm s (^∀ p)) := depthAdmission_ranked e _ ha.1
  have he : RankedEnvironment (simPushFree e) := rankedEnvironment_push e har.1
  obtain ⟨_,_,hbase,hreserve⟩ := simPushFree_fields e
  have hsize : ((1 : M)+1)+1 < (^∀ p) := by
    change ((1 : M)+1)+1 < pair (6 : M) p + 1
    have h6 : ((1 : M)+1)+1 ≤ (6 : M) := by norm_num
    exact lt_of_le_of_lt (le_trans h6 (le_pair_left (6 : M) p)) (lt_add_one _)
  have hb := rankedAdmission_axiomReserve e s (^∀ p) har
  have hlt := add_lt_add_left hsize (simBase e)
  have hslack : ((simBase e+1)+1)+1 < simReserve e := by
    apply lt_of_lt_of_le _ hb
    simpa only [add_assoc,add_comm,add_left_comm] using hlt
  have hpush : (simBase (simPushFree e)+1)+1 < simReserve (simPushFree e) := by
    rw [hbase,hreserve]
    exact hslack
  have hop := simRuleSeparation_ranked (simPushFree e) φ hφ he hpush
  rw [← hopen] at hop
  exact tp_mp (tp_gen (simBase e) hop) (simRuleAll_general e s p hs hm)
#print axioms simRuleSeparation_closedOnce_ranked
end models
end PA194ModelLogic
