import PA194PAeqTypedFormulaBound
import PA194NameVariableFull
import PA194ClosedInductionEnvironment
import PA194ForwardSymmetryRoot
import PA194ForwardTransitivityRoot
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open PA194ContextSpecializeCode PA194ContextModusPonensCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance eqclosedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqclosedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqclosedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqclosedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqclosedLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqclosedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194ForwardReflProof PA194ClosedEnvironment PA194FormulaDispatcher PA194PAeqBind
noncomputable local instance : adjunctiveFullSepTheory.Δ₁ := adjunctiveFullSepTheoryDelta


theorem fullSource_symmetry_guarded :
    GDerivable adjunctiveFullSepTheory ({tr (⌜PA194PAeq.symmetry⌝ : M)} : M) := by
  let φ : M := ⌜PA194PAeq.symmetry⌝
  have hp : IsSemiformula PA194PAeq.language 0 φ := by
    dsimp [φ]
    simpa using (Semiformula.quote_isSemiformula PA194PAeq.symmetry : IsSemiformula PA194PAeq.language (0 : M) (⌜PA194PAeq.symmetry⌝ : M))
  have hfree : PA194PAeq.symmetry.freeVariables = ∅ := by decide
  have hz : PA194PAeqBind.formulaFreeBound φ = 0 := by
    dsimp [φ]
    rw [PA194PAeqBind.formulaFreeBound_quote_fvSup]
    simp [Semiformula.fvSup,hfree]
  have he := closedTranslate_packets hp.isUFormula hz (rootParameters_valid φ) (idParam_identity (φ+1)).1
  have hr := PA194ForwardSymmetry.root_symmetry_provable (M := M)
    (⌜PA194PAeq.symmetry.univCl⌝ : M) (rootParameters_length (⌜PA194PAeq.symmetry.univCl⌝ : M))
  have hquote : (⌜PA194PAeq.symmetry.univCl⌝ : M) = φ := by
    rw [Sentence.quote_def,PA194ForwardSymmetry.typed_symmetry_closed]
  have hr' : Provable adjunctiveFullSepTheory (translateFormula (rootParameters φ) φ) := by
    simpa only [hquote] using hr
  have htr : Provable adjunctiveFullSepTheory (tr φ) := by
    change Provable adjunctiveFullSepTheory (translateFormula (idParam (φ+1)) φ)
    rw [←he]
    exact hr'
  refine ⟨0, ?_⟩
  simpa [guards_zero] using htr.toDerivable


theorem fullSource_transitivity_guarded :
    GDerivable adjunctiveFullSepTheory ({tr (⌜PA194PAeq.transitivity⌝ : M)} : M) := by
  let φ : M := ⌜PA194PAeq.transitivity⌝
  have hp : IsSemiformula PA194PAeq.language 0 φ := by
    dsimp [φ]
    simpa using (Semiformula.quote_isSemiformula PA194PAeq.transitivity : IsSemiformula PA194PAeq.language (0 : M) (⌜PA194PAeq.transitivity⌝ : M))
  have hfree : PA194PAeq.transitivity.freeVariables = ∅ := by decide
  have hz : PA194PAeqBind.formulaFreeBound φ = 0 := by
    dsimp [φ]
    rw [PA194PAeqBind.formulaFreeBound_quote_fvSup]
    simp [Semiformula.fvSup,hfree]
  have he := closedTranslate_packets hp.isUFormula hz (rootParameters_valid φ) (idParam_identity (φ+1)).1
  have hr := PA194ForwardTransitivity.root_transitivity_provable (M := M)
    (⌜PA194PAeq.transitivity.univCl⌝ : M) (rootParameters_length (⌜PA194PAeq.transitivity.univCl⌝ : M))
  have hquote : (⌜PA194PAeq.transitivity.univCl⌝ : M) = φ := by
    rw [Sentence.quote_def,PA194ForwardTransitivity.typed_transitivity_closed]
  have hr' : Provable adjunctiveFullSepTheory (translateFormula (rootParameters φ) φ) := by
    simpa only [hquote] using hr
  have htr : Provable adjunctiveFullSepTheory (tr φ) := by
    change Provable adjunctiveFullSepTheory (translateFormula (idParam (φ+1)) φ)
    rw [←he]
    exact hr'
  refine ⟨0, ?_⟩
  simpa [guards_zero] using htr.toDerivable

#print axioms fullSource_symmetry_guarded
#print axioms fullSource_transitivity_guarded
end models
end PA194GuardedCompiler
