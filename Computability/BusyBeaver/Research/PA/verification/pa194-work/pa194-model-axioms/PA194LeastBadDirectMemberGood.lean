import PA194TraceDirectMember
import PA194TraceMemberBackwardCode
import PA194LeastExcludesInstances
import PA194OrdinalBadNotZeroCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194LeastBadDirectMemberGood
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceDirectSyntax PA194TraceDirectAt PA194TraceDirectMember PA194LeastExcludesClosedModel PA194FullSepWitnessBranch PA194FixedSyntaxQuote PA194TraceMemberBackwardCode PA194LeastExcludesInstances PA194LeastExcludesAtCode PA194LeastExcludesClosedTemplate PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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

/-- A member below the least bad point is good, given its source membership. -/
noncomputable def leastBadDirectMemberGoodCode (p s c b m g dt ds du hd hl hm : M) : M :=
  let np := neg SourceL p
  let prop := substs1 SourceL (^&m) p
  let target := insert prop g
  let tr := traceDirectRoot np s c
  let src := memberFvarCode m s
  let univ := (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : M)
  let dom := substs1 SourceL (^&b) (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
  let lv := (?[ ^&m, ^&b, ^&c] : M)
  let least := subst SourceL lv (⌜leastCB3⌝ : M)
  let bm := memberFvarCode m b
  let cm := memberFvarCode m c
  let wt := wkRule (insert tr target) dt
  let ws := wkRule (insert src target) ds
  let wu := wkRule (insert univ target) du
  let wd := wkRule (insert dom target) hd
  let wl := wkRule (insert least target) hl
  let wm := wkRule (insert bm target) hm
  let bad := axL (insert (neg SourceL prop) target) prop
  let pos := directMemberBackwardCode np s c m target wt ws bad
  let neg := leastExcludesAtCode c b m target wu wd wl wm
  cutRule target cm pos neg

noncomputable def leastBadDirectMemberGoodGraph : 𝚺₁.Semisentence 13 := .mkSigma
  “out p s c b m g dt ds du hd hl hm. ∃ np, !(negGraph SourceL) np p ∧
    ∃ tm, !qqFvarDef tm m ∧ ∃ tb, !qqFvarDef tb b ∧ ∃ tc, !qqFvarDef tc c ∧
    ∃ prop, !(substs1Graph SourceL) prop tm p ∧ ∃ target, !insertDef target prop g ∧
    ∃ tr, !traceDirectRootGraph tr np s c ∧
    ∃ src, !memberFvarGraph src m s ∧
    ∃ univ, !(fixedFormulaQuoteGraph (∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)) univ ∧
    ∃ domain, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) domain ∧ ∃ dom, !(substs1Graph SourceL) dom tb domain ∧
    ∃ lt, !(fixedFormulaQuoteGraph leastCB3) lt ∧ ∃ v1, !adjoinDef v1 tc 0 ∧ ∃ v2, !adjoinDef v2 tb v1 ∧ ∃ vec, !adjoinDef vec tm v2 ∧
    ∃ least, !(substsGraph SourceL) least vec lt ∧ ∃ bm, !memberFvarGraph bm m b ∧ ∃ cm, !memberFvarGraph cm m c ∧
    ∃ ts, !insertDef ts tr target ∧ ∃ wt, !wkRuleGraph wt ts dt ∧ ∃ ss, !insertDef ss src target ∧ ∃ ws, !wkRuleGraph ws ss ds ∧
    ∃ us, !insertDef us univ target ∧ ∃ wu, !wkRuleGraph wu us du ∧ ∃ ds0, !insertDef ds0 dom target ∧ ∃ wd, !wkRuleGraph wd ds0 hd ∧
    ∃ ls, !insertDef ls least target ∧ ∃ wl, !wkRuleGraph wl ls hl ∧ ∃ ms, !insertDef ms bm target ∧ ∃ wm, !wkRuleGraph wm ms hm ∧
    ∃ nprop, !(negGraph SourceL) nprop prop ∧ ∃ bads, !insertDef bads nprop target ∧ ∃ bad, !axLGraph bad bads prop ∧
    ∃ pos, !directMemberBackwardGraph pos np s c m target wt ws bad ∧
    ∃ ng, !leastExcludesAtGraph ng c b m target wu wd wl wm ∧ !cutRuleGraph out target cm pos ng”

theorem leastBadDirectMemberGoodGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 12 → M => leastBadDirectMemberGoodCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)) leastBadDirectMemberGoodGraph := by
  haveI := traceDirectRootGraph_defined (M := M)
  haveI := memberFvarGraph_defined (M := M)
  haveI := directMemberBackwardGraph_defined (M := M)
  haveI := leastExcludesAtGraph_defined (M := M)
  exact .mk fun v => by simp [leastBadDirectMemberGoodGraph,leastBadDirectMemberGoodCode,fixedFormulaQuoteGraph_correct]

noncomputable def leastBadDirectMemberGoodProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar m]) Γ := by
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  let N : Semiformula M SourceL 1 := ⟨neg SourceL p, by simpa using hp.neg⟩
  let prop : Formula M SourceL := P.subst ![Semiterm.fvar m]
  let ni : Formula M SourceL := N.subst ![Semiterm.fvar m]
  let tr : Formula M SourceL := (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL)
  let src : Formula M SourceL := Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar s]
  let univ : Formula M SourceL := ⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝
  let dom : Formula M SourceL := (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]
  let least : Formula M SourceL := (⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]
  let bm : Formula M SourceL := Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]
  let cm : Formula M SourceL := Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar c]
  let target := insert prop Γ
  let wt : T ⊢!ᵈᵉʳ insert tr target := TDerivation.wk dt (by intro x hx; simp [target] at hx ⊢; tauto)
  let ws : T ⊢!ᵈᵉʳ insert src target := TDerivation.wk ds (by intro x hx; simp [target] at hx ⊢; tauto)
  let wu : T ⊢!ᵈᵉʳ insert univ target := TDerivation.wk du (by intro x hx; simp [target] at hx ⊢; tauto)
  let wd : T ⊢!ᵈᵉʳ insert dom target := TDerivation.wk hd (by intro x hx; simp [target] at hx ⊢; tauto)
  let wl : T ⊢!ᵈᵉʳ insert least target := TDerivation.wk hl (by intro x hx; simp [target] at hx ⊢; tauto)
  let wm : T ⊢!ᵈᵉʳ insert bm target := TDerivation.wk hm (by intro x hx; simp [target] at hx ⊢; tauto)
  let bad : T ⊢!ᵈᵉʳ insert (∼prop) target := TDerivation.em prop (by simp [target]) (by simp)
  have he : ni = ∼prop := by
    have hN : N = ∼P := by apply Semiformula.ext; rfl
    simp [ni,prop,hN]
  let bad' := TDerivation.cast (congrArg (fun q => insert q target) he.symm) bad
  let pos := directMemberBackwardProof T target (neg SourceL p) s c m hp.neg wt ws bad'
  let neg := leastExcludesAlignedProof T target c b m wu wd wl wm
  exact TDerivation.cut pos neg

@[simp] theorem leastBadDirectMemberGoodProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p s c b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (ds : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    (leastBadDirectMemberGoodProof T Γ p s c b m hp dt ds du hd hl hm).val =
      leastBadDirectMemberGoodCode p s c b m Γ.val dt.val ds.val du.val hd.val hl.val hm.val := by
  have hr (y : M) : ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar y] : Formula M SourceL)).val = memberFvarCode m y := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [leastBadDirectMemberGoodProof,leastBadDirectMemberGoodCode,TDerivation.cut_val,
    directMemberBackwardProof_val,leastExcludesAlignedProof_val,TDerivation.wk_val,TDerivation.em_val,TDerivation.cast_val,
    Sequent.val_insert,Bootstrapping.Semiformula.val_substs,Bootstrapping.Semiformula.val_shift,
    Bootstrapping.Semiformula.val_neg,Bootstrapping.Semiformula.free_val,Bootstrapping.Semiterm.fvar_val,
    SemitermVec.val_succ,hr,substs1,Semiformula.quote_def]
  simp [Matrix.vecHead,Matrix.vecTail]

/-- The full source theory supplies the fixed least-exclusion theorem. -/
noncomputable def leastBadDirectMemberGoodFromTheory (Γ : Sequent M SourceL) (p s c b m : M)
    (hp : IsSemiformula SourceL 1 p)
    (dt : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (⟨traceDirectRoot (neg SourceL p) s c, traceDirectRoot_scoped _ _ _ hp.neg⟩ : Formula M SourceL) Γ)
    (ds : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hd : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hm : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar m]) Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let uq : Formula M SourceL := ⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝
  let du : T ⊢!ᵈᵉʳ insert uq Γ := TDerivation.wk (leastExcludesUniversalProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  exact leastBadDirectMemberGoodProof T Γ p s c b m hp dt ds du hd hl hm

#print axioms leastBadDirectMemberGoodFromTheory
#print axioms leastBadDirectMemberGoodProof_val
#print axioms leastBadDirectMemberGoodGraph_defined
#print axioms leastBadDirectMemberGoodProof
end models
end PA194LeastBadDirectMemberGood
