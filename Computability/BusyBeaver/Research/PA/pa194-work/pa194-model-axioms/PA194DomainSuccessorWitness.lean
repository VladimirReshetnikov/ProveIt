import PA194DomainSuccessorAt
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
namespace PA194DomainSuccessorWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainSuccessorAt PA194InternalInductionBaseShift PA194GreatestSuccessorAtCode PA194DomainGreatestAtCode PA194DomainGreatestClosedTemplate PA194ContextExsWitnessCode PA194ContextExsElimCode PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def domainSuccessorPair2 : Semiproposition M6.PA.RelationalSource.language 2 :=
  domain (.bvar 0) ⋏ successor (.bvar 1) (.bvar 0)

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

/-- The domain-successor existential has this one-bound-variable body. -/
noncomputable def domainSuccessorWitnessBody (x : M) : Semiformula M SourceL 1 :=
  (⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst (SemitermVec.q ![Semiterm.fvar x])

theorem domainSuccessorExists_eq_ex (x : M) :
    ((⌜domainSuccessorExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x] : Formula M SourceL) =
      ∃⁰ domainSuccessorWitnessBody x := by
  have hs : domainSuccessorExistsTemplate = ∃⁰ domainSuccessorPair2 := by
    simp [domainSuccessorExistsTemplate,domainSuccessorPair2,domainSuccessorExists]
  have ht : (⌜domainSuccessorExistsTemplate⌝ : Semiformula M SourceL 1) = ∃⁰ (⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2) := by
    rw [hs]
    simp
  rw [ht]
  simp [domainSuccessorWitnessBody]

theorem domainSuccessorWitness_free (x : M) :
    (domainSuccessorWitnessBody x).free =
      (⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (x+1)] := by
  have hfix : (⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).shift = ⌜domainSuccessorPair2⌝ := by
    apply Semiformula.ext
    exact typed_quote_shift_fixed domainSuccessorPair2 (by decide)
  simp [domainSuccessorWitnessBody,Bootstrapping.Semiformula.free,Semiformula.shift_substs,Semiformula.substs_substs,SemitermVec.q,hfix]

noncomputable def domainSuccessorWitnessCode (x : M) : M :=
  subst SourceL (qVec SourceL (?[ ^&x] : M)) (⌜domainSuccessorPair2⌝ : M)

noncomputable def domainSuccessorWitnessGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out x. ∃ t, !qqFvarDef t x ∧ ∃ vec, !adjoinDef vec t 0 ∧ ∃ q, !(qVecGraph SourceL) q vec ∧
    ∃ gt, !(fixedFormulaQuoteGraph domainSuccessorPair2) gt ∧ !(substsGraph SourceL) out q gt”

theorem domainSuccessorWitnessGraph_defined :
    𝚺₁-Function₁ (domainSuccessorWitnessCode : M → M) via domainSuccessorWitnessGraph := by
  exact .mk fun v => by simp [domainSuccessorWitnessGraph,domainSuccessorWitnessCode,fixedFormulaQuoteGraph_correct]

noncomputable def domainSuccessorWitnessElimCode (x q g de db : M) : M :=
  contextExsElimCode (domainSuccessorWitnessCode x) q g de db

noncomputable def domainSuccessorWitnessElimGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out x q g de db. ∃ body, !domainSuccessorWitnessGraph body x ∧ !contextExsElimGraph out body q g de db”

theorem domainSuccessorWitnessElimGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => domainSuccessorWitnessElimCode (v 0) (v 1) (v 2) (v 3) (v 4)) domainSuccessorWitnessElimGraph := by
  haveI := domainSuccessorWitnessGraph_defined (M := M)
  haveI := contextExsElimGraph_defined (M := M)
  exact .mk fun v => by simp [domainSuccessorWitnessElimGraph,domainSuccessorWitnessElimCode]

noncomputable def domainSuccessorWitnessElimProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x : M) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜domainSuccessorExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (x+1)])) Γ.shift)) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let de' := TDerivation.cast (congrArg (fun q => insert q Γ) (domainSuccessorExists_eq_ex x)) de
  let db' := TDerivation.cast (congrArg (fun q' => insert q.shift (insert (∼q') Γ.shift)) (domainSuccessorWitness_free x).symm) db
  exact PA194ContextExsWitnessCode.contextExsElimWitness T Γ (domainSuccessorWitnessBody x) q de' db'

@[simp] theorem domainSuccessorWitnessElimProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (x : M) (q : Formula M SourceL)
    (de : T ⊢!ᵈᵉʳ insert ((⌜domainSuccessorExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ)
    (db : T ⊢!ᵈᵉʳ insert q.shift (insert (∼((⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar 0,Semiterm.fvar (x+1)])) Γ.shift)) :
    (domainSuccessorWitnessElimProof T Γ x q de db).val = domainSuccessorWitnessElimCode x q.val Γ.val de.val db.val := by
  simp [domainSuccessorWitnessElimProof,domainSuccessorWitnessElimCode,domainSuccessorWitnessCode,domainSuccessorWitnessBody,
    SemitermVec.val_succ,qVec,Semiformula.quote_def]

theorem domainSuccessorPair_at (a b : M) :
    ((⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) ⋏
      ((⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) := by
  have he : (⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2) =
      (⌜domainZero⌝ : Semiformula M SourceL 2) ⋏ (⌜successorTemplate⌝ : Semiformula M SourceL 2) := by
    simp [domainSuccessorPair2,domainZero,successorTemplate]
  rw [he]
  simp [domainZeroAt a b]

noncomputable def domainSuccessorPartCode (left : Bool) (a b g d : M) : M :=
  let dom := substs1 SourceL (^&b) (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
  let succ := subst SourceL (?[ ^&b, ^&a] : M) (⌜successorTemplate⌝ : M)
  if left then contextAndLeftCode dom succ g d else contextAndRightCode dom succ g d

noncomputable def domainSuccessorDomainGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out a b g d. ∃ ta, !qqFvarDef ta a ∧ ∃ tb, !qqFvarDef tb b ∧ ∃ tail, !adjoinDef tail ta 0 ∧ ∃ vec, !adjoinDef vec tb tail ∧
    ∃ dt, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dt ∧ ∃ st, !(fixedFormulaQuoteGraph successorTemplate) st ∧
    ∃ dom, !(substs1Graph SourceL) dom tb dt ∧ ∃ succ, !(substsGraph SourceL) succ vec st ∧
    !contextAndLeftGraph out dom succ g d”
noncomputable def domainSuccessorRelationGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out a b g d. ∃ ta, !qqFvarDef ta a ∧ ∃ tb, !qqFvarDef tb b ∧ ∃ tail, !adjoinDef tail ta 0 ∧ ∃ vec, !adjoinDef vec tb tail ∧
    ∃ dt, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dt ∧ ∃ st, !(fixedFormulaQuoteGraph successorTemplate) st ∧
    ∃ dom, !(substs1Graph SourceL) dom tb dt ∧ ∃ succ, !(substsGraph SourceL) succ vec st ∧
    !contextAndRightGraph out dom succ g d”

theorem domainSuccessorDomainGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => domainSuccessorPartCode true (v 0) (v 1) (v 2) (v 3)) domainSuccessorDomainGraph := by
  haveI := contextAndLeftGraph_defined (M := M)
  exact .mk fun v => by simp [domainSuccessorDomainGraph,domainSuccessorPartCode,fixedFormulaQuoteGraph_correct,substs1]

theorem domainSuccessorRelationGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => domainSuccessorPartCode false (v 0) (v 1) (v 2) (v 3)) domainSuccessorRelationGraph := by
  haveI := contextAndRightGraph_defined (M := M)
  exact .mk fun v => by simp [domainSuccessorRelationGraph,domainSuccessorPartCode,fixedFormulaQuoteGraph_correct,substs1]

noncomputable def domainSuccessorDomainProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (d : T ⊢!ᵈᵉʳ insert ((⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ := by
  let dom : Formula M SourceL := (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]
  let succ : Formula M SourceL := (⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]
  let d' := TDerivation.cast (congrArg (fun f => insert f Γ) (domainSuccessorPair_at a b)) d
  exact contextAndLeftProof T Γ dom succ d'

noncomputable def domainSuccessorRelationProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (d : T ⊢!ᵈᵉʳ insert ((⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ := by
  let dom : Formula M SourceL := (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]
  let succ : Formula M SourceL := (⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]
  let d' := TDerivation.cast (congrArg (fun f => insert f Γ) (domainSuccessorPair_at a b)) d
  exact contextAndRightProof T Γ dom succ d'

@[simp] theorem domainSuccessorDomainProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (d : T ⊢!ᵈᵉʳ insert ((⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    (domainSuccessorDomainProof T Γ a b d).val = domainSuccessorPartCode true a b Γ.val d.val := by
  simp [domainSuccessorDomainProof,domainSuccessorPartCode,Semiformula.quote_def,SemitermVec.val_succ,substs1]

@[simp] theorem domainSuccessorRelationProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (d : T ⊢!ᵈᵉʳ insert ((⌜domainSuccessorPair2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    (domainSuccessorRelationProof T Γ a b d).val = domainSuccessorPartCode false a b Γ.val d.val := by
  simp [domainSuccessorRelationProof,domainSuccessorPartCode,Semiformula.quote_def,SemitermVec.val_succ,substs1]

#print axioms domainSuccessorPair_at
#print axioms domainSuccessorDomainGraph_defined
#print axioms domainSuccessorRelationGraph_defined
#print axioms domainSuccessorDomainProof
#print axioms domainSuccessorRelationProof
#print axioms domainSuccessorDomainProof_val
#print axioms domainSuccessorRelationProof_val
#print axioms domainSuccessorWitnessGraph_defined
#print axioms domainSuccessorWitnessElimGraph_defined
#print axioms domainSuccessorWitnessElimProof
#print axioms domainSuccessorWitnessElimProof_val
#print axioms domainSuccessorExists_eq_ex
#print axioms domainSuccessorWitness_free
end models
end PA194DomainSuccessorWitness
