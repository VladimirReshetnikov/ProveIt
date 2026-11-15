import PA194GreatestSuccessorAtCode
import PA194DomainGreatestAtCode
import PA194ContextExsWitnessCode
import PA194FullSepWitnessBranch
import PA194DomainInstances
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194GreatestWitnessOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194InternalInductionBaseShift PA194GreatestSuccessorAtCode PA194DomainGreatestAtCode PA194DomainGreatestClosedTemplate PA194ContextExsWitnessCode PA194ContextExsElimCode PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

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

open M6.PA.RelationalSource

open M6.PA.RelationalSource

/-- The greatest-element existential has this one-bound-variable body. -/
noncomputable def greatestWitnessBody (x : M) : Semiformula M SourceL 1 :=
  (⌜greatestBM2⌝ : Semiformula M SourceL 2).subst (SemitermVec.q ![Semiterm.fvar x])

theorem greatestExists_eq_ex (x : M) :
    ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x] : Formula M SourceL) =
      ∃⁰ greatestWitnessBody x := by
  have hs : greatestExistsTemplate = ∃⁰ greatestBM2 := by
    simp [greatestExistsTemplate,greatestBM2,greatestExists]
  have ht : (⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1) = ∃⁰ (⌜greatestBM2⌝ : Semiformula M SourceL 2) := by
    rw [hs]
    simp
  rw [ht]
  simp [greatestWitnessBody]

theorem greatestWitness_free (x : M) :
    (greatestWitnessBody x).free =
      (⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (x+1)] := by
  have hfix : (⌜greatestBM2⌝ : Semiformula M SourceL 2).shift = ⌜greatestBM2⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed greatestBM2 (by decide)
  simp [greatestWitnessBody,Bootstrapping.Semiformula.free,Semiformula.shift_substs,Semiformula.substs_substs,SemitermVec.q,hfix]

noncomputable def greatestWitnessCode (x : M) : M :=
  subst SourceL (qVec SourceL (?[ ^&x] : M)) (⌜greatestBM2⌝ : M)

noncomputable def greatestWitnessGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out x. ∃ t, !qqFvarDef t x ∧ ∃ vec, !adjoinDef vec t 0 ∧ ∃ q, !(qVecGraph SourceL) q vec ∧
    ∃ gt, !(fixedFormulaQuoteGraph greatestBM2) gt ∧ !(substsGraph SourceL) out q gt”

theorem greatestWitnessGraph_defined :
    𝚺₁-Function₁ (greatestWitnessCode : M → M) via greatestWitnessGraph := by
  exact .mk fun v => by simp [greatestWitnessGraph,greatestWitnessCode,fixedFormulaQuoteGraph_correct]

noncomputable def greatestWitnessElimCode (x q g de db : M) : M :=
  contextExsElimCode (greatestWitnessCode x) q g de db

noncomputable def greatestWitnessElimGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out x q g de db. ∃ body, !greatestWitnessGraph body x ∧ !contextExsElimGraph out body q g de db”

theorem greatestWitnessElimGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => greatestWitnessElimCode (v 0) (v 1) (v 2) (v 3) (v 4)) greatestWitnessElimGraph := by
  haveI := greatestWitnessGraph_defined (M := M)
  haveI := contextExsElimGraph_defined (M := M)
  exact .mk fun v => by simp [greatestWitnessElimGraph,greatestWitnessElimCode]

noncomputable def greatestWitnessElimProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x : M) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (x+1)])) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let de' := TDerivation.cast (congrArg (fun q => insert q Γ) (greatestExists_eq_ex x)) de
  let db' := TDerivation.cast (congrArg (fun q' => insert q.shift (insert (∼q') Γ.shift)) (greatestWitness_free x).symm) db
  exact PA194ContextExsWitnessCode.contextExsElimWitness T Γ (greatestWitnessBody x) q de' db'

@[simp] theorem greatestWitnessElimProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x : M) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (x+1)])) Γ.shift)) :
    (greatestWitnessElimProof T Γ x q de db).val = greatestWitnessElimCode x q.val Γ.val de.val db.val := by
  simp [greatestWitnessElimProof,greatestWitnessElimCode,greatestWitnessCode,greatestWitnessBody,
    SemitermVec.val_succ,qVec,Semiformula.quote_def]

#print axioms greatestWitnessGraph_defined
#print axioms greatestWitnessElimGraph_defined
#print axioms greatestWitnessElimProof
#print axioms greatestWitnessElimProof_val
#print axioms greatestExists_eq_ex
#print axioms greatestWitness_free
end models
end PA194GreatestWitnessOpen
