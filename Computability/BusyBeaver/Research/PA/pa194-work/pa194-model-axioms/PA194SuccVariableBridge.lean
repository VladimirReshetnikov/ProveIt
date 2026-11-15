import PA194LeastExcludesClosedModel
import PA194FullSepWitnessBranch
import PA194ForwardSuccValueUniversal
import PA194SuccVariableTemplate
import PA194ContextIffApplicationCode
import PA194ContextTripleSpecializeCode
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194SuccVariableBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194FullSepWitnessBranch PA194LeastExcludesClosedModel PA194LeastExcludesClosedTemplate PA194ContextTripleSpecializeCode PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

open PA194ForwardSuccValueUniversal PA194ForwardSuccValueTemplate PA194ContextIffApplicationCode
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

open PA194ForwardSuccValueAt PA194SuccVariableTemplate PA194SuccVariableDispatcher PA194PAeqOrdinalValues PA194TermDispatcher

noncomputable def dispatcherSuccValue (x z : M) : M :=
  translate (succVariablePacket x z) (^func (1 : M) 1 (?[ ^#(0 : M)] : M))

theorem dispatcherSuccValue_scoped (x z : M) : IsSemiformula SourceL 0 (dispatcherSuccValue x z) := by
  rw [dispatcherSuccValue,numericalDispatcher_eq_template]
  simpa using (((⌜translatedSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z] : Formula M SourceL).isSemiformula)

theorem dispatcherSuccValue_eq (x z : M) :
    (⟨dispatcherSuccValue x z,dispatcherSuccValue_scoped x z⟩ : Formula M SourceL) =
      (⌜translatedSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z] := by
  apply Semiformula.ext
  exact numericalDispatcher_eq_template x z

noncomputable def dispatcherSuccForwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x z : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dh : T ⊢!ᵈᵉʳ insert (⟨dispatcherSuccValue x z,dispatcherSuccValue_scoped x z⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜directSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) Γ := by
  let dh' := TDerivation.cast (congrArg (fun q => insert q Γ) (dispatcherSuccValue_eq x z)) dh
  exact succValueForwardProof T Γ x z du dh'

noncomputable def dispatcherSuccBackwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x z : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dh : T ⊢!ᵈᵉʳ insert ((⌜directSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) Γ) :
    T ⊢!ᵈᵉʳ insert (⟨dispatcherSuccValue x z,dispatcherSuccValue_scoped x z⟩ : Formula M SourceL) Γ := by
  let out := succValueBackwardProof T Γ x z du dh
  exact TDerivation.cast (congrArg (fun q => insert q Γ) (dispatcherSuccValue_eq x z).symm) out

@[simp] theorem dispatcherSuccForwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x z : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dh : T ⊢!ᵈᵉʳ insert (⟨dispatcherSuccValue x z,dispatcherSuccValue_scoped x z⟩ : Formula M SourceL) Γ) :
    (dispatcherSuccForwardProof T Γ x z du dh).val = succValueAtCode true x z Γ.val du.val dh.val := by
  simp [dispatcherSuccForwardProof]

@[simp] theorem dispatcherSuccBackwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x z : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dh : T ⊢!ᵈᵉʳ insert ((⌜directSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) Γ) :
    (dispatcherSuccBackwardProof T Γ x z du dh).val = succValueAtCode false x z Γ.val du.val dh.val := by
  simp [dispatcherSuccBackwardProof]

#print axioms dispatcherSuccValue_scoped
#print axioms dispatcherSuccValue_eq
#print axioms dispatcherSuccForwardProof_val
#print axioms dispatcherSuccBackwardProof_val
end models
end PA194SuccVariableBridge
