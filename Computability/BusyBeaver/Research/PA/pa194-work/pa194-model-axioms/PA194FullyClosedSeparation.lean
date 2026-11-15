import PA194FreeBoundClosed
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
local instance freeBoundClosedLeafZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundClosedLeafOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundClosedLeafAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundClosedLeafMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundClosedLeafLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundClosedLeafIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Close exactly the available free-index range of an internal separation root. -/
noncomputable def fullyClosedSeparation (φ : M) : M :=
  modelClose (formulaFreeBound (sepRoot φ)) (sepRoot φ)

theorem fullyClosedSeparation_sentence (φ : M) (hφ : IsSemiformula SourceL 1 φ) :
    IsSemiformula SourceL 0 (fullyClosedSeparation φ) ∧
      shift SourceL (fullyClosedSeparation φ) = fullyClosedSeparation φ :=
  closedSeparation_FVFree φ hφ

theorem fullyClosedSeparation_leaf (bound reserve e s φ : M)
    (hφ : IsSemiformula SourceL 1 φ)
    (ha : SeedAdmission bound reserve e (axm s (fullyClosedSeparation φ))) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (fullyClosedSeparation φ)) 1) :=
  modelClose_separation_leaf_unconditional_size bound reserve _ e s φ hφ ha

#print axioms fullyClosedSeparation_sentence
#print axioms fullyClosedSeparation_leaf
end models
end PA194BindSource
