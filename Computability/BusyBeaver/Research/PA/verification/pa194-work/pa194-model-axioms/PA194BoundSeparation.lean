import PA194BindFormulaInverse
import PA194ClosedSeparationRank
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
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sepRoot_scoped (φ : M) (hφ : IsSemiformula SourceL 1 φ) :
    IsSemiformula SourceL 0 (sepRoot φ) := by
  have hφ3 : IsSemiformula SourceL 3 φ := ⟨hφ.isUFormula, le_trans hφ.bv_le (by norm_num)⟩
  have hnφ3 : IsSemiformula SourceL 3 (neg SourceL φ) := (IsSemiformula.neg_iff).2 hφ3
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have h01 : IsSemitermVec SourceL 2 3 (relExtVector (0 : M) (1 : M)) := by
    simp [relExtVector, ←adjoin_def]
  have h02 : IsSemitermVec SourceL 2 3 (relExtVector (0 : M) (2 : M)) := by
    simp [relExtVector, ←adjoin_def]
    norm_num
  simp only [sepRoot,IsSemiformula.all,IsSemiformula.exs,zero_add]
  have hthree : (1 : M)+1+1 = 3 := by norm_num
  rw [hthree]
  simp only [sepInner,IsSemiformula.and,IsSemiformula.or,IsSemiformula.rel,IsSemiformula.nrel]
  exact ⟨⟨⟨hr,h01⟩,⟨⟨hr,h02⟩,hφ3⟩⟩,⟨⟨⟨hr,h02⟩,hnφ3⟩,⟨hr,h01⟩⟩⟩

/-- Close the first free parameter in any internal separation instance. -/
noncomputable def oneBoundSeparation (φ : M) : M := ^∀ (bindFormula 0 (sepRoot φ))

theorem oneBoundSeparation_leaf (bound reserve e s φ : M)
    (hφ : IsSemiformula SourceL 1 φ)
    (hs : IsFormulaSet SourceL s) (hm : oneBoundSeparation φ ∈ s)
    (ha : SeedAdmission bound reserve e (axm s (oneBoundSeparation φ))) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (oneBoundSeparation φ)) 1) := by
  have hroot := sepRoot_scoped φ hφ
  have hopen := (bindFormula_scope_open (sepRoot φ) hroot).2
  exact simRuleSeparation_closedOnce_ranked bound reserve e s (bindFormula 0 (sepRoot φ)) φ
    hs hm hφ hopen ha
#print axioms sepRoot_scoped
#print axioms oneBoundSeparation_leaf
end models
end PA194BindSource
