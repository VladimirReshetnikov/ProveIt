import PA194PAeqTypedFormulaBound
import PA194NameVariableExistence
import PA194NameVariableReflexive
import PA194ForwardReflRoot
import PA194ClosedInductionEnvironment
import PA194ContextSpecializeCode
import PA194ContextModusPonensCode
import PA194FullSepOpen
import DiophantineConsistency.PRAModelIOpenPairing
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
local instance evarFullZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance evarFullOne : One M := ⟨F oneCode Fin.elim0⟩
local instance evarFullAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance evarFullMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance evarFullLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance evarFullIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194ForwardReflProof PA194ClosedEnvironment PA194FormulaDispatcher PA194PAeqBind
noncomputable local instance : adjunctiveFullSepTheory.Δ₁ := adjunctiveFullSepTheoryDelta
noncomputable def variableFullTheory : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩

theorem reflexivity_quote_code : (⌜PA194PAeq.reflexivity⌝ : M) = ^∀ (reflexiveBody : M) := by
  change (⌜∀⁰ (PA194PAeq.eq (.bvar 0) (.bvar 0))⌝ : M) = _
  rw [Semiformula.quote_all]
  congr 1

theorem reflexivity_closed_quote_code : (⌜PA194PAeq.reflexivity.univCl⌝ : M) = ^∀ (reflexiveBody : M) := by
  rw [Sentence.quote_def,PA194ForwardReflProof.typed_reflexivity_closed]
  exact reflexivity_quote_code

theorem reflexivity_code_freeBound : PA194PAeqBind.formulaFreeBound (^∀ (reflexiveBody : M)) = 0 := by
  rw [←reflexivity_quote_code,formulaFreeBound_quote_fvSup]
  have hfree : PA194PAeq.reflexivity.freeVariables = ∅ := by decide
  simp [Semiformula.fvSup, hfree]

theorem fullSource_reflexivity_provable : Provable adjunctiveFullSepTheory (tr (^∀ (reflexiveBody : M))) := by
  let φ : M := ^∀ reflexiveBody
  have hp : IsSemiformula PA194PAeq.language 0 φ := IsSemiformula.all.mpr (by simpa using (reflexiveBody_valid (M := M)))
  have hfv : PA194PAeqBind.formulaFreeBound φ = 0 := reflexivity_code_freeBound
  have he := closedTranslate_packets hp.isUFormula hfv (rootParameters_valid φ) (idParam_identity (φ+1)).1
  have hr := root_reflexivity_provable (M := M) (⌜PA194PAeq.reflexivity.univCl⌝ : M)
    (rootParameters_length (⌜PA194PAeq.reflexivity.univCl⌝ : M))
  have hr' : Provable adjunctiveFullSepTheory (translateFormula (rootParameters φ) φ) := by
    simpa only [φ,reflexivity_closed_quote_code] using hr
  change Provable adjunctiveFullSepTheory (translateFormula (idParam (φ+1)) φ)
  rw [←he]
  exact hr'

noncomputable def fullSource_reflexivityProof : (variableFullTheory (M := M)) ⊢!
    (⟨tr (^∀ (reflexiveBody : M)),tr_valid (IsSemiformula.all.mpr (by simpa using (reflexiveBody_valid (M := M))))⟩ : Formula M SourceL) := by
  apply Derivable.toTDerivation
  obtain ⟨d, hd⟩ := fullSource_reflexivity_provable (M := M)
  exact ⟨d, by simpa [variableFullTheory, Proof, ←singleton_eq_insert] using hd⟩

theorem fullSource_eVar : ∀ i : M, GDerivable adjunctiveFullSepTheory ({tr (exName (^&i))} : M) :=
  eVar_of_guarded_reflexivity (guarded_reflexivity_of_closed (variableFullTheory (M := M)) (fullSource_reflexivityProof (M := M)))

#print axioms reflexivity_quote_code
#print axioms reflexivity_closed_quote_code
#print axioms reflexivity_code_freeBound
#print axioms fullSource_reflexivity_provable
#print axioms fullSource_eVar
end models
end PA194GuardedCompiler
