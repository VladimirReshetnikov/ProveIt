import PA194ModelClosureDefinable
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance repeatSepLeafZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance repeatSepLeafOne : One M := ⟨F oneCode Fin.elim0⟩
local instance repeatSepLeafAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance repeatSepLeafMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance repeatSepLeafLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance repeatSepLeafIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem modelPush_zero (e : M) : modelPush 0 e = e := by
  simp [modelPush, pushIterConstruction]

@[simp] theorem modelPush_succ (n e : M) : modelPush (n+1) e = simPushFree (modelPush n e) := by
  simp [modelPush, pushIterConstruction]

theorem modelPush_fields (n e : M) :
    simBase (modelPush n e) = simBase e + n ∧ simReserve (modelPush n e) = simReserve e := by
  haveI : 𝚺₁-Function₂ (modelPush : M → M → M) := modelPush_definable
  have hdef : 𝚺₁-Predicate (fun n : M =>
      simBase (modelPush n e) = simBase e + n ∧ simReserve (modelPush n e) = simReserve e) := by
    unfold simBase simReserve
    definability
  induction n using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => simp
  case succ n ih =>
    rw [modelPush_succ]
    obtain ⟨_,_,hb,hr⟩ := simPushFree_fields (modelPush n e)
    rw [hb,hr,ih.1,ih.2]
    constructor
    · simp [add_assoc]
    · rfl

theorem modelPush_ranked (n e : M) (he : RankedEnvironment e) :
    RankedEnvironment (modelPush n e) := by
  haveI : 𝚺₁-Function₂ (modelPush : M → M → M) := modelPush_definable
  have hdef : 𝚺₁-Predicate (fun n : M => RankedEnvironment (modelPush n e)) := by
    unfold RankedEnvironment simFree simBase
    definability
  induction n using ISigma1.sigma1_succ_induction
  · exact hdef
  case zero => simpa using he
  case succ n ih => simpa using rankedEnvironment_push _ ih

/-- Repeatedly close a separation root, given ranked resources at the final pushed environment. -/
theorem modelClose_separation_leaf (n e φ : M)
    (hφ : IsSemiformula SourceL 1 φ)
    (he : RankedEnvironment (modelPush n e))
    (hreserve : ((simBase (modelPush n e) + 1) + 1) < simReserve (modelPush n e)) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (modelClose n (sepRoot φ))) 1) := by
  have hroot := sepRoot_scoped φ hφ
  have ht := simRuleSeparation_ranked (modelPush n e) φ hφ he hreserve
  exact modelClose_leaf n e (sepRoot φ) hroot ht

/-- A seeded axiom supplies all resources when its code dominates the binder count. -/
theorem modelClose_separation_leaf_seeded (bound reserve n e s φ : M)
    (hφ : IsSemiformula SourceL 1 φ)
    (ha : SeedAdmission bound reserve e (axm s (modelClose n (sepRoot φ))))
    (hsize : (n+1)+1 < modelClose n (sepRoot φ)) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (modelClose n (sepRoot φ))) 1) := by
  have har := depthAdmission_ranked e _ ha.1
  have he := modelPush_ranked n e har.1
  have hb := rankedAdmission_axiomReserve e s (modelClose n (sepRoot φ)) har
  have hlt := add_lt_add_left hsize (simBase e)
  have hslack : ((simBase e+n)+1)+1 < simReserve e := by
    apply lt_of_lt_of_le _ hb
    simpa only [add_assoc,add_comm,add_left_comm] using hlt
  obtain ⟨hbase,hreserve⟩ := modelPush_fields n e
  have hpush : ((simBase (modelPush n e)+1)+1) < simReserve (modelPush n e) := by
    rw [hbase,hreserve]
    exact hslack
  exact modelClose_separation_leaf n e φ hφ he hpush

#print axioms modelClose_separation_leaf_seeded
#print axioms modelPush_fields
#print axioms modelPush_ranked
#print axioms modelClose_separation_leaf
end models
end PA194BindSource
