import PA194DomainLeastAt
import PA194LeastDummyIndex
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
namespace PA194LeastWitnessOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainLeastAt PA194LeastDummyIndex PA194LeastExcludesAtCode PA194InternalInductionBaseShift PA194GreatestSuccessorAtCode PA194DomainGreatestAtCode PA194DomainGreatestClosedTemplate PA194ContextExsWitnessCode PA194ContextExsElimCode PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- The least-element existential has this one-bound-variable body. -/
noncomputable def leastWitnessBody (x : M) : Semiformula M SourceL 1 :=
  (⌜leastCB2⌝ : Semiformula M SourceL 2).subst (SemitermVec.q ![Semiterm.fvar x])

theorem leastExists_eq_ex (x : M) :
    ((⌜leastExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x] : Formula M SourceL) =
      ∃⁰ leastWitnessBody x := by
  have hs : leastExistsTemplate = ∃⁰ leastCB2 := by
    simp [leastExistsTemplate,leastCB2,leastExists]
  have ht : (⌜leastExistsTemplate⌝ : Semiformula M SourceL 1) = ∃⁰ (⌜leastCB2⌝ : Semiformula M SourceL 2) := by
    rw [hs]
    simp
  rw [ht]
  simp [leastWitnessBody]

theorem leastWitness_free (x : M) :
    (leastWitnessBody x).free =
      (⌜leastCB2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (x+1)] := by
  have hfix : (⌜leastCB2⌝ : Semiformula M SourceL 2).shift = ⌜leastCB2⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed leastCB2 (by decide)
  simp [leastWitnessBody,Bootstrapping.Semiformula.free,Semiformula.shift_substs,Semiformula.substs_substs,SemitermVec.q,hfix]

noncomputable def leastWitnessCode (x : M) : M :=
  subst SourceL (qVec SourceL (?[ ^&x] : M)) (⌜leastCB2⌝ : M)

noncomputable def leastWitnessGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out x. ∃ t, !qqFvarDef t x ∧ ∃ vec, !adjoinDef vec t 0 ∧ ∃ q, !(qVecGraph SourceL) q vec ∧
    ∃ gt, !(fixedFormulaQuoteGraph leastCB2) gt ∧ !(substsGraph SourceL) out q gt”

theorem leastWitnessGraph_defined :
    𝚺₁-Function₁ (leastWitnessCode : M → M) via leastWitnessGraph := by
  exact .mk fun v => by simp [leastWitnessGraph,leastWitnessCode,fixedFormulaQuoteGraph_correct]

noncomputable def leastWitnessElimCode (x q g de db : M) : M :=
  contextExsElimCode (leastWitnessCode x) q g de db

noncomputable def leastWitnessElimGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out x q g de db. ∃ body, !leastWitnessGraph body x ∧ !contextExsElimGraph out body q g de db”

theorem leastWitnessElimGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => leastWitnessElimCode (v 0) (v 1) (v 2) (v 3) (v 4)) leastWitnessElimGraph := by
  haveI := leastWitnessGraph_defined (M := M)
  haveI := contextExsElimGraph_defined (M := M)
  exact .mk fun v => by simp [leastWitnessElimGraph,leastWitnessElimCode]

noncomputable def leastWitnessElimProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x : M) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜leastExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜leastCB2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (x+1)])) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let de' := TDerivation.cast (congrArg (fun q => insert q Γ) (leastExists_eq_ex x)) de
  let db' := TDerivation.cast (congrArg (fun q' => insert q.shift (insert (∼q') Γ.shift)) (leastWitness_free x).symm) db
  exact PA194ContextExsWitnessCode.contextExsElimWitness T Γ (leastWitnessBody x) q de' db'

@[simp] theorem leastWitnessElimProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x : M) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜leastExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜leastCB2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (x+1)])) Γ.shift)) :
    (leastWitnessElimProof T Γ x q de db).val = leastWitnessElimCode x q.val Γ.val de.val db.val := by
  simp [leastWitnessElimProof,leastWitnessElimCode,leastWitnessCode,leastWitnessBody,
    SemitermVec.val_succ,qVec,Semiformula.quote_def]

/-- The first index in the three-variable least template is immaterial. -/
theorem leastWitness_free_aligned (c a : M) :
    (leastWitnessBody c).free =
      (⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar 0,Semiterm.fvar (c+1)] := by
  have hs : leastCB3 = leastCB2 ⇜ ![#1,#2] := by
    simp [leastCB3,leastCB2]
    ordinalSyntax
  have ht : (⌜leastCB3⌝ : Semiformula M SourceL 3) =
      (⌜leastCB2⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 1,Semiterm.bvar 2] := by
    rw [hs, Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht,leastWitness_free]
  simp [Semiformula.substs_substs]

noncomputable def leastWitnessAlignedElimProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a : M) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜leastExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar 0,Semiterm.fvar (c+1)])) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let de' := TDerivation.cast (congrArg (fun f => insert f Γ) (leastExists_eq_ex c)) de
  let db' := TDerivation.cast (congrArg (fun f => insert q.shift (insert (∼f) Γ.shift)) (leastWitness_free_aligned c a).symm) db
  exact PA194ContextExsWitnessCode.contextExsElimWitness T Γ (leastWitnessBody c) q de' db'

@[simp] theorem leastWitnessAlignedElimProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a : M) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜leastExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar 0,Semiterm.fvar (c+1)])) Γ.shift)) :
    (leastWitnessAlignedElimProof T Γ c a q de db).val = leastWitnessElimCode c q.val Γ.val de.val db.val := by
  simp [leastWitnessAlignedElimProof,leastWitnessElimCode,leastWitnessCode,leastWitnessBody,
    SemitermVec.val_succ,qVec,Semiformula.quote_def]

#print axioms leastWitness_free_aligned
#print axioms leastWitnessAlignedElimProof
#print axioms leastWitnessAlignedElimProof_val
#print axioms leastWitnessGraph_defined
#print axioms leastWitnessElimGraph_defined
#print axioms leastWitnessElimProof
#print axioms leastWitnessElimProof_val
#print axioms leastExists_eq_ex
#print axioms leastWitness_free
end models
end PA194LeastWitnessOpen
