import PA194ModelNumericalSeedSim

/-! General target witness and seeded existential-introduction rule. -/
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
local instance genericRefutationZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance genericRefutationOne : One M := ⟨F oneCode Fin.elim0⟩
local instance genericRefutationAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance genericRefutationMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance genericRefutationLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance genericRefutationIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A source theory refutation compiles once every internal axiom has a target supplier. -/
theorem numericalSeed_refutation_target (T : Theory SourceL) [T.Δ₁] (d : M)
    (h : Proof T d (^⊥ : M))
    (axiomRule : ∀ reserve e s p : M, SeedAdmission 0 reserve e (axm s p) → p ∈ T.Δ₁Class →
      numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1)) :
    TargetProvable (1 : M) := by
  let reserve : M := ((d+1)+1)+(d+1)
  let C := Classical.choice (seedCompilerAdmission_exists (0 : M) reserve)
  let S := numericalSeedSim T reserve C (axiomRule reserve)
  let e : M := linearSeed 0 reserve (d+1)
  have ha : SeedAdmission 0 reserve e d := by
    simpa only [e,reserve] using seedAdmission_initial (0 : M) d
  have he : e ≤ S.bound := C.allBounded e d ha
  have ht : TargetProvable (impValue (negatedTranslation e (^⊥ : M)) (1 : M)) :=
    S.proof h he ha
  rw [negatedTranslation_any,fixedFormulaTranslation_falsum] at ht
  exact tp_mp (imp_refl (1 : M)) ht

#print axioms numericalSeed_refutation_target
end models
end PA194ModelLogic
