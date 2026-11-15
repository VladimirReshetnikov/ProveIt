import PA194FullSepTheory
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open PA194ModelLogic
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance fullSepTheoryModelZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance fullSepTheoryModelOne : One M := ⟨F oneCode Fin.elim0⟩
local instance fullSepTheoryModelAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance fullSepTheoryModelMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance fullSepTheoryModelLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance fullSepTheoryModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem fullSepUniform_model (q : M) :
    M ⊧/![q] fullSepUniform.val ↔
      ∃ p : M, IsSemiformula SourceL 1 p ∧ fullyClosedSeparation p = q := by
  letI : 𝚫₁-Predicate (fullSepPure : M → Prop) via fullSepUniform := fullSepUniform_defined
  have hv : M ⊧/![q] fullSepUniform.val ↔ fullSepPure q := by
    simpa using (HierarchySymbol.Defined.iff (φ := fullSepUniform) (v := ![q]))
  rw [hv]
  constructor
  · rintro ⟨_,p,_,hp,he⟩
    exact ⟨p,hp,(pureFullyClosedSeparation_model p).symm.trans he⟩
  · rintro ⟨p,hp,rfl⟩
    refine ⟨(fullyClosedSeparation_sentence p hp).2,p,?_,hp,?_⟩
    · simpa only [pureFullyClosedSeparation_model] using pureFullyClosed_property_bound p hp
    · exact pureFullyClosedSeparation_model p

theorem fullSepTheory_class (q : M) :
    letI := fullSepTheoryDelta
    q ∈ fullSepTheory.Δ₁Class ↔
      ∃ p : M, IsSemiformula SourceL 1 p ∧ fullyClosedSeparation p = q := by
  letI := fullSepTheoryDelta
  change M ⊧/![q] fullSepUniform.val ↔ _
  exact fullSepUniform_model q

theorem fullSepTheory_axiom_seed (reserve e s q : M)
    (ha : SeedAdmission 0 reserve e (axm s q))
    (hq : letI := fullSepTheoryDelta; q ∈ fullSepTheory.Δ₁Class) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e q) 1) := by
  letI := fullSepTheoryDelta
  obtain ⟨p,hp,rfl⟩ := (fullSepTheory_class q).mp hq
  exact fullyClosedSeparation_leaf 0 reserve e s p hp ha

#print axioms fullSepUniform_model
#print axioms fullSepTheory_class
#print axioms fullSepTheory_axiom_seed
end models
end PA194BindSource
