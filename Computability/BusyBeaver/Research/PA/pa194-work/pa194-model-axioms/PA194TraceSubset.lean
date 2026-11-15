import PA194TraceDirectShift
import PA194TraceDirectMember
import PA194ContextAllCode
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
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace PA194TraceSubset
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceDirectShift PA194TraceDirectMember PA194TraceDirectSyntax PA194ContextAllCode PA194InternalInductionBaseShift PA194GreatestSuccessorAtCode PA194DomainGreatestAtCode PA194DomainGreatestClosedTemplate PA194ContextExsWitnessCode PA194ContextExsElimCode PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def subsetCS2 : Semiproposition M6.PA.RelationalSource.language 2 := subset (.bvar 1) (.bvar 0)

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

noncomputable def subsetBody (s c : M) : Semiformula M SourceL 1 :=
  let mc : Semiformula M SourceL 1 := Semiformula.rel Relation.mem ![Semiterm.bvar 0,Semiterm.fvar c]
  let ms : Semiformula M SourceL 1 := Semiformula.rel Relation.mem ![Semiterm.bvar 0,Semiterm.fvar s]
  ∼mc ⋎ ms

theorem subsetAt_eq_all (s c : M) :
    ((⌜subsetCS2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar s,Semiterm.fvar c] : Formula M SourceL) = ∀⁰ subsetBody s c := by
  have hs : subsetCS2 = ∀⁰ (mem (.bvar 2) (.bvar 0) 🡒 mem (.bvar 1) (.bvar 0)) := by simp [subsetCS2,subset]
  rw [hs]
  simp [subsetBody,mem,Semiformula.imp_def,sourceImply,Semiformula.typedQuote,SemitermVec.q,Matrix.cons_val,Matrix.vecHead,Matrix.vecTail]

theorem subsetBody_free (s c : M) :
    (subsetBody s c).free =
      ((∼(Semiformula.rel Relation.mem ![Semiterm.fvar 0,Semiterm.fvar (c+1)] : Formula M SourceL)) ⋎
       (Semiformula.rel Relation.mem ![Semiterm.fvar 0,Semiterm.fvar (s+1)] : Formula M SourceL)) := by
  simp [subsetBody,Bootstrapping.Semiformula.free,Semiformula.shift_substs,SemitermVec.q]

/-- Every represented trace is a subset of its source. -/
noncomputable def traceSubsetProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜subsetCS2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar s,Semiterm.fvar c]) Γ := by
  let mc : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar 0,Semiterm.fvar (c+1)]
  let ms : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar 0,Semiterm.fvar (s+1)]
  let prop : Formula M SourceL := (⟨shift SourceL p, by simpa using hp.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar 0]
  let Δ : Sequent M SourceL := insert (∼mc) Γ.shift
  let tr0 := shiftDirectTraceProof T Γ p s c hp d
  let tr : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (shift SourceL p) (s+1) (c+1), traceDirectRoot_scoped _ _ _ hp.shift⟩ : Formula M SourceL) Δ := TDerivation.wk tr0 (by intro x hx; simp [Δ] at hx ⊢; tauto)
  let member : T ⊢!ᵈᵉʳ insert mc Δ := TDerivation.em mc (by simp [Δ]) (by simp [Δ])
  let pair := directMemberForwardProof T Δ (shift SourceL p) (s+1) (c+1) 0 hp.shift tr member
  let dms := contextAndLeftProof T Δ ms prop pair
  have he : insert ms Δ = insert (∼mc) (insert ms Γ.shift) := by
    apply Sequent.ext
    intro x
    simp [Δ]
    tauto
  let dms' := TDerivation.cast he dms
  let target := insert (∼mc ⋎ ms) Γ.shift
  let dmw : T ⊢!ᵈᵉʳ insert (∼mc) (insert ms target) := TDerivation.wk dms' (by intro x hx; simp [target] at hx ⊢; tauto)
  let disj : T ⊢!ᵈᵉʳ target := TDerivation.or' (by simp [target]) dmw
  let body : Semiformula M SourceL 1 := subsetBody s c
  let disj' := TDerivation.cast (congrArg (fun f => insert f Γ.shift) (subsetBody_free s c).symm) disj
  let out := contextAllProof T Γ body disj'
  exact TDerivation.cast (congrArg (fun f => insert f Γ) (subsetAt_eq_all s c).symm) out

noncomputable def subsetBodyCode (s c : M) : M :=
  let mc := ^rel (2 : M) (1 : M) (?[ ^#(0 : M), ^&c] : M)
  let ms := ^rel (2 : M) (1 : M) (?[ ^#(0 : M), ^&s] : M)
  neg SourceL mc ^⋎ ms

theorem subsetBody_val (s c : M) : (subsetBody s c).val = subsetBodyCode s c := by
  have hm (y : M) : ((Semiformula.rel Relation.mem ![Semiterm.bvar 0,Semiterm.fvar y]) : Semiformula M SourceL 1).val =
      ^rel (2 : M) (1 : M) (?[ ^#(0 : M), ^&y] : M) := by
    simp [SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [subsetBody,subsetBodyCode,Bootstrapping.Semiformula.val_or,Bootstrapping.Semiformula.val_neg,hm]

noncomputable def traceSubsetCode (p s c g d : M) : M :=
  let sp := shift SourceL p
  let ss := s+1
  let sc := c+1
  let mc := memberFvarCode 0 sc
  let ms := memberFvarCode 0 ss
  let prop := substs1 SourceL (^&(0 : M)) sp
  let Δ := insert (neg SourceL mc) (setShift SourceL g)
  let tr := wkRule (insert (traceDirectRoot sp ss sc) Δ) (shiftDirectTraceProofCode p s c g d)
  let dm := axL (insert mc Δ) mc
  let pair := directMemberForwardCode sp ss sc 0 Δ tr dm
  let dms := contextAndLeftCode ms prop Δ pair
  let target := insert (neg SourceL mc ^⋎ ms) (setShift SourceL g)
  let dmw := wkRule (insert (neg SourceL mc) (insert ms target)) dms
  let disj := orIntro target (neg SourceL mc) ms dmw
  contextAllCode (subsetBodyCode s c) g disj

noncomputable def subsetBodyGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out s c. ∃ z, !qqBvarDef z 0 ∧ ∃ tc, !qqFvarDef tc c ∧ ∃ ts, !qqFvarDef ts s ∧
    ∃ vc1, !adjoinDef vc1 tc 0 ∧ ∃ vc, !adjoinDef vc z vc1 ∧ ∃ mc, !qqRelDef mc 2 1 vc ∧
    ∃ vs1, !adjoinDef vs1 ts 0 ∧ ∃ vs, !adjoinDef vs z vs1 ∧ ∃ ms, !qqRelDef ms 2 1 vs ∧
    ∃ nmc, !(negGraph SourceL) nmc mc ∧ !qqOrDef out nmc ms”

theorem subsetBodyGraph_defined : 𝚺₁-Function₂ (subsetBodyCode : M → M → M) via subsetBodyGraph := by
  exact .mk fun v => by simp [subsetBodyGraph,subsetBodyCode]

noncomputable def traceSubsetGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out p s c g d. ∃ sp, !(shiftGraph SourceL) sp p ∧ ∃ ss, ss = s+1 ∧ ∃ sc, sc = c+1 ∧
    ∃ mc, !memberFvarGraph mc 0 sc ∧ ∃ ms, !memberFvarGraph ms 0 ss ∧ ∃ z, !qqFvarDef z 0 ∧
    ∃ prop, !(substs1Graph SourceL) prop z sp ∧ ∃ nmc, !(negGraph SourceL) nmc mc ∧
    ∃ sg, !(setShiftGraph SourceL) sg g ∧ ∃ delta, !insertDef delta nmc sg ∧
    ∃ trf, !traceDirectRootGraph trf sp ss sc ∧ ∃ sh, !shiftDirectTraceProofGraph sh p s c g d ∧
    ∃ trseq, !insertDef trseq trf delta ∧ ∃ tr, !wkRuleGraph tr trseq sh ∧
    ∃ dmseq, !insertDef dmseq mc delta ∧ ∃ dm, !axLGraph dm dmseq mc ∧
    ∃ pair, !directMemberForwardGraph pair sp ss sc 0 delta tr dm ∧
    ∃ dms, !contextAndLeftGraph dms ms prop delta pair ∧ ∃ dis, !qqOrDef dis nmc ms ∧
    ∃ target, !insertDef target dis sg ∧ ∃ mt, !insertDef mt ms target ∧ ∃ dseq, !insertDef dseq nmc mt ∧
    ∃ dmw, !wkRuleGraph dmw dseq dms ∧ ∃ dp, !orIntroGraph dp target nmc ms dmw ∧
    ∃ body, !subsetBodyGraph body s c ∧ !contextAllGraph out body g dp”

theorem traceSubsetGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => traceSubsetCode (v 0) (v 1) (v 2) (v 3) (v 4)) traceSubsetGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := traceDirectRootGraph_defined (M := M)
  haveI := shiftDirectTraceProofGraph_defined (M := M)
  haveI := directMemberForwardGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  haveI := subsetBodyGraph_defined (M := M)
  haveI := contextAllGraph_defined (M := M)
  exact .mk fun v => by simp [traceSubsetGraph,traceSubsetCode,substs1]

#print axioms subsetBodyGraph_defined
#print axioms traceSubsetGraph_defined

@[simp] theorem traceSubsetProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s c : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot p s c, traceDirectRoot_scoped p s c hp⟩ : Formula M SourceL) Γ) :
    (traceSubsetProof T Γ p s c hp d).val = traceSubsetCode p s c Γ.val d.val := by
  have hm (y : M) : ((Semiformula.rel Relation.mem ![Semiterm.fvar 0,Semiterm.fvar y]) : Formula M SourceL).val = memberFvarCode 0 y := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [traceSubsetProof,traceSubsetCode,contextAllProof_val,subsetBody_val,TDerivation.cast_val,TDerivation.or'_val,
    TDerivation.wk_val,TDerivation.em_val,contextAndLeftProof_val,directMemberForwardProof_val,shiftDirectTraceProof_val,
    Sequent.val_insert,Sequent.shift,Bootstrapping.Semiformula.val_or,Bootstrapping.Semiformula.val_neg,
    Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hm,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms subsetBody_val
#print axioms traceSubsetProof_val
#print axioms traceSubsetProof
#print axioms subsetAt_eq_all
#print axioms subsetBody_free
end models
end PA194TraceSubset
