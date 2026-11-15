import PA194FullSepTheoryModel
import PA194ModelClosedSepUniform
import PA194ModelFairness
import PA194ModelClosedSepClassifier
import PA194ModelSeedEnvironment
import PA194ModelNumericalSeedRefutation

/-! Internal structural induction for arbitrary-label vacuity. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194BindSource
open PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable PA194SchedulerHaltCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
/-- Finite adjunctive axioms together with classifier-defined closed separation. -/
noncomputable def adjunctiveFullSepTheory : Theory SourceL :=
  adjunctiveTheory ∪ fullSepTheory

@[implicit_reducible] noncomputable def adjunctiveFullSepTheoryDelta : adjunctiveFullSepTheory.Δ₁ := by
  letI := adjunctiveTheoryDelta
  letI := fullSepTheoryDelta
  exact Theory.Δ₁.add adjunctiveTheoryDelta fullSepTheoryDelta

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance adjunctiveFullSepModelZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance adjunctiveFullSepModelOne : One M := ⟨F oneCode Fin.elim0⟩
local instance adjunctiveFullSepModelAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance adjunctiveFullSepModelMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance adjunctiveFullSepModelLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance adjunctiveFullSepModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem adjunctiveFullSepTheory_class (p : M) :
    letI := adjunctiveFullSepTheoryDelta
    letI := adjunctiveTheoryDelta
    p ∈ adjunctiveFullSepTheory.Δ₁Class ↔
      p ∈ adjunctiveTheory.Δ₁Class ∨
      ∃ φ : M, IsSemiformula SourceL 1 φ ∧ fullyClosedSeparation φ = p := by
  letI := adjunctiveTheoryDelta
  letI := fullSepTheoryDelta
  letI := adjunctiveFullSepTheoryDelta
  change M ⊧/![p] (adjunctiveTheory.Δ₁ch ⋎ fullSepTheory.Δ₁ch).val ↔ _
  have hcases :
      M ⊧/![p] (adjunctiveTheory.Δ₁ch ⋎ fullSepTheory.Δ₁ch).val ↔
      (M ⊧/![p] adjunctiveTheory.Δ₁ch.val) ∨ (M ⊧/![p] fullSepTheory.Δ₁ch.val) := by
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
  rw [hcases]
  exact or_congr Iff.rfl (fullSepTheory_class p)

theorem adjunctiveFullSep_refutation_target (d : M)
    (hd : letI := adjunctiveFullSepTheoryDelta; Proof adjunctiveFullSepTheory d (^⊥ : M)) :
    TargetProvable (1 : M) := by
  letI := adjunctiveFullSepTheoryDelta
  apply numericalSeed_refutation_target adjunctiveFullSepTheory d hd
  intro reserve e s q ha hq
  rcases (adjunctiveFullSepTheory_class q).mp hq with hfixed | ⟨p,hp,rfl⟩
  · exact simRuleAdjunctiveAxiom_seed 0 reserve e s q ha hfixed
  · exact fullyClosedSeparation_leaf 0 reserve e s p hp ha

theorem adjunctiveFullSep_provable_halts
    (h : letI := adjunctiveFullSepTheoryDelta; Provable adjunctiveFullSepTheory (^⊥ : M)) :
    ∃ k : M, F haltAfter ![k] = 1 := by
  letI := adjunctiveFullSepTheoryDelta
  obtain ⟨d,hd⟩ := h
  exact PA194ModelFairness.provable_halts (adjunctiveFullSep_refutation_target d hd)

theorem adjunctiveFullSep_consistent_of_nonhalting
    (hnh : ∀ k : M, F haltAfter ![k] ≠ 1) :
    letI := adjunctiveFullSepTheoryDelta; ¬ Provable adjunctiveFullSepTheory (^⊥ : M) := by
  letI := adjunctiveFullSepTheoryDelta
  intro h
  obtain ⟨k,hk⟩ := adjunctiveFullSep_provable_halts h
  exact hnh k hk

#print axioms adjunctiveFullSepTheoryDelta
#print axioms adjunctiveFullSepTheory_class
#print axioms adjunctiveFullSep_refutation_target
#print axioms adjunctiveFullSep_provable_halts
#print axioms adjunctiveFullSep_consistent_of_nonhalting
end models
end PA194BindSource
