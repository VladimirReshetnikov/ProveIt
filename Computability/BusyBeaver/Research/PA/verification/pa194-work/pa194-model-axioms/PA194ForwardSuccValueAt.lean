import PA194LeastExcludesClosedModel
import PA194FullSepWitnessBranch
import PA194ForwardSuccValueUniversal
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
namespace PA194ForwardSuccValueAt
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

def translatedSuccValue2 : Semiproposition M6.PA.RelationalSource.language 2 :=
  PA194ForwardTyped.value (PA194PAeq.succ (.bvar 0)) ![.bvar 0] (fun i => .fvar i) (.bvar 1)
def directSuccValue2 : Semiproposition M6.PA.RelationalSource.language 2 :=
  Ordinal.domain (.bvar 0) ⋏ (Ordinal.domain (.bvar 1) ⋏ Ordinal.successor (.bvar 0) (.bvar 1))

noncomputable def succValueAtCode (forward : Bool) (x z ctx du dh : M) : M :=
  let vec := (?[ ^&x, ^&z] : M)
  let lhs := subst SourceL vec (⌜translatedSuccValue2⌝ : M)
  let rhs := subst SourceL vec (⌜directSuccValue2⌝ : M)
  let eqv := contextDoubleCode (⌜successorValueNormalizationBound⌝ : M) (^&x) (^&z) ctx du
  if forward then contextIffForwardCode lhs rhs ctx eqv dh else contextIffBackwardCode lhs rhs ctx eqv dh

noncomputable def succValueForwardGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out x z ctx du dh. ∃ bt, !(fixedFormulaQuoteGraph successorValueNormalizationBound) bt ∧
    ∃ lt, !(fixedFormulaQuoteGraph translatedSuccValue2) lt ∧ ∃ rt, !(fixedFormulaQuoteGraph directSuccValue2) rt ∧
    ∃ vx, !qqFvarDef vx x ∧ ∃ vz, !qqFvarDef vz z ∧ ∃ v1, !adjoinDef v1 vz 0 ∧ ∃ vec, !adjoinDef vec vx v1 ∧
    ∃ lhs, !(substsGraph SourceL) lhs vec lt ∧ ∃ rhs, !(substsGraph SourceL) rhs vec rt ∧
    ∃ eqv, !contextDoubleGraph eqv bt vx vz ctx du ∧ !contextIffForwardGraph out lhs rhs ctx eqv dh”

noncomputable def succValueBackwardGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out x z ctx du dh. ∃ bt, !(fixedFormulaQuoteGraph successorValueNormalizationBound) bt ∧
    ∃ lt, !(fixedFormulaQuoteGraph translatedSuccValue2) lt ∧ ∃ rt, !(fixedFormulaQuoteGraph directSuccValue2) rt ∧
    ∃ vx, !qqFvarDef vx x ∧ ∃ vz, !qqFvarDef vz z ∧ ∃ v1, !adjoinDef v1 vz 0 ∧ ∃ vec, !adjoinDef vec vx v1 ∧
    ∃ lhs, !(substsGraph SourceL) lhs vec lt ∧ ∃ rhs, !(substsGraph SourceL) rhs vec rt ∧
    ∃ eqv, !contextDoubleGraph eqv bt vx vz ctx du ∧ !contextIffBackwardGraph out lhs rhs ctx eqv dh”

theorem succValueForwardGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 5 → M => succValueAtCode true (w 0) (w 1) (w 2) (w 3) (w 4)) succValueForwardGraph := by
  haveI := contextDoubleGraph_defined (M := M)
  haveI := contextIffForwardGraph_defined (M := M)
  exact .mk fun w => by simp [succValueForwardGraph,succValueAtCode,fixedFormulaQuoteGraph_correct]

theorem succValueBackwardGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 5 → M => succValueAtCode false (w 0) (w 1) (w 2) (w 3) (w 4)) succValueBackwardGraph := by
  haveI := contextDoubleGraph_defined (M := M)
  haveI := contextIffBackwardGraph_defined (M := M)
  exact .mk fun w => by simp [succValueBackwardGraph,succValueAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def succValueEqvProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x z : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((((⌜translatedSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) 🡒
      ((⌜directSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z])) ⋏
      (((⌜directSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) 🡒
      ((⌜translatedSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]))) Γ := by
  let body : Semiformula M SourceL 2 := ⌜successorValueNormalizationBound⌝
  let lhs : Semiformula M SourceL 2 := ⌜translatedSuccValue2⌝
  let rhs : Semiformula M SourceL 2 := ⌜directSuccValue2⌝
  have hb : body = (lhs 🡒 rhs) ⋏ (rhs 🡒 lhs) := by
    change (⌜sourceIff translatedSuccValue2 directSuccValue2⌝ : Semiformula M SourceL 2) =
      ((⌜translatedSuccValue2⌝ : Semiformula M SourceL 2) 🡒 ⌜directSuccValue2⌝) ⋏
      ((⌜directSuccValue2⌝ : Semiformula M SourceL 2) 🡒 ⌜translatedSuccValue2⌝)
    change Semiformula.typedQuote M (sourceIff translatedSuccValue2 directSuccValue2) = _
    simp only [sourceIff,sourceImply,Semiformula.imp_def,Semiformula.typedQuote]
    have hl : Semiformula.typedQuote M (Semiformula.neg translatedSuccValue2) = ∼(⌜translatedSuccValue2⌝ : Semiformula M SourceL 2) := by
      exact Semiformula.typedQuote_neg translatedSuccValue2
    have hr : Semiformula.typedQuote M (Semiformula.neg directSuccValue2) = ∼(⌜directSuccValue2⌝ : Semiformula M SourceL 2) := by
      exact Semiformula.typedQuote_neg directSuccValue2
    rw [hl,hr]
    rfl
  have hu : (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ ∀⁰ body := by simp [body]
  let du' := TDerivation.cast (congrArg (fun q => insert q Γ) hu) du
  let ds := contextDoubleProof T Γ body (Semiterm.fvar x) (Semiterm.fvar z) du'
  have he : (body.subst ![Semiterm.fvar x,Semiterm.fvar z] : Formula M SourceL) =
      ((lhs.subst ![Semiterm.fvar x,Semiterm.fvar z] 🡒 rhs.subst ![Semiterm.fvar x,Semiterm.fvar z]) ⋏
       (rhs.subst ![Semiterm.fvar x,Semiterm.fvar z] 🡒 lhs.subst ![Semiterm.fvar x,Semiterm.fvar z])) := by
    rw [hb]; simp
  exact TDerivation.cast (congrArg (fun q => insert q Γ) he) ds

noncomputable def succValueForwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x z : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dh : T ⊢!ᵈᵉʳ insert ((⌜translatedSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜directSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) Γ :=
  contextIffForwardProof T Γ _ _ (succValueEqvProof T Γ x z du) dh

noncomputable def succValueBackwardProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x z : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dh : T ⊢!ᵈᵉʳ insert ((⌜directSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜translatedSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) Γ :=
  contextIffBackwardProof T Γ _ _ (succValueEqvProof T Γ x z du) dh

@[simp] theorem succValueForwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x z : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dh : T ⊢!ᵈᵉʳ insert ((⌜translatedSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) Γ) :
    (succValueForwardProof T Γ x z du dh).val = succValueAtCode true x z Γ.val du.val dh.val := by
  simp [succValueForwardProof,succValueEqvProof,succValueAtCode,Semiformula.quote_def,SemitermVec.val_succ]

@[simp] theorem succValueBackwardProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x z : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorValueNormalizationBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dh : T ⊢!ᵈᵉʳ insert ((⌜directSuccValue2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar x,Semiterm.fvar z]) Γ) :
    (succValueBackwardProof T Γ x z du dh).val = succValueAtCode false x z Γ.val du.val dh.val := by
  simp [succValueBackwardProof,succValueEqvProof,succValueAtCode,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms succValueForwardGraph_defined
#print axioms succValueBackwardGraph_defined
#print axioms succValueForwardProof_val
#print axioms succValueBackwardProof_val
#print axioms succValueEqvProof
end models
end PA194ForwardSuccValueAt
