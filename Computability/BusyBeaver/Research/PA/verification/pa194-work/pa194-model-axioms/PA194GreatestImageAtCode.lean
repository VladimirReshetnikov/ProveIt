import PA194LeastExcludesClosedModel
import PA194FullSepWitnessBranch
import PA194ContextFiveSpecializeCode
import PA194OrderIsoGreatestUniversal
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
namespace PA194GreatestImageAtCode
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

def domainB3 : Semiproposition M6.PA.RelationalSource.language 3 := domain (.bvar 1)
def leastCB3 : Semiproposition M6.PA.RelationalSource.language 3 := least (.bvar 2) (.bvar 1)
def memberBM3 : Semiproposition M6.PA.RelationalSource.language 3 := mem (.bvar 1) (.bvar 0)
def memberCM3 : Semiproposition M6.PA.RelationalSource.language 3 := mem (.bvar 2) (.bvar 0)

open M6.PA.RelationalSource.PairGraph PA194ContextFiveSpecializeCode PA194OrderIsoGreatestUniversal PA194OrderIsoGreatestTemplate
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

def bijectionBound5 : Semiproposition M6.PA.RelationalSource.language 5 :=
  orderBijection (.bvar 0) (.bvar 1) (.bvar 2)
def sourceGreatestBound5 : Semiproposition M6.PA.RelationalSource.language 5 :=
  Ordinal.greatest (.bvar 1) (.bvar 3)
def graphEdgeBound5 : Semiproposition M6.PA.RelationalSource.language 5 :=
  edge (.bvar 0) (.bvar 3) (.bvar 4)
def targetGreatestBound5 : Semiproposition M6.PA.RelationalSource.language 5 :=
  Ordinal.greatest (.bvar 2) (.bvar 4)

noncomputable def greatestImageAtCode (g a b x y ctx du dhb dhg dhe : M) : M :=
  let vec := (?[ ^&g, ^&a, ^&b, ^&x, ^&y] : M)
  let bij := subst SourceL vec (⌜bijectionBound5⌝ : M)
  let src := subst SourceL vec (⌜sourceGreatestBound5⌝ : M)
  let edg := subst SourceL vec (⌜graphEdgeBound5⌝ : M)
  let dst := subst SourceL vec (⌜targetGreatestBound5⌝ : M)
  let imp3 := neg SourceL edg ^⋎ dst
  let imp2 := neg SourceL src ^⋎ imp3
  let sp := contextFiveCode (⌜greatestImageBound⌝ : M) (^&g) (^&a) (^&b) (^&x) (^&y) ctx du
  let r1 := contextMPCode bij imp2 ctx sp dhb
  let r2 := contextMPCode src imp3 ctx r1 dhg
  contextMPCode edg dst ctx r2 dhe

noncomputable def greatestImageAtGraph : 𝚺₁.Semisentence 11 := .mkSigma
  “out g a b x y ctx du dhb dhg dhe.
    ∃ body, !(fixedFormulaQuoteGraph greatestImageBound) body ∧
    ∃ jb, !(fixedFormulaQuoteGraph bijectionBound5) jb ∧ ∃ sg, !(fixedFormulaQuoteGraph sourceGreatestBound5) sg ∧
    ∃ ge, !(fixedFormulaQuoteGraph graphEdgeBound5) ge ∧ ∃ tg, !(fixedFormulaQuoteGraph targetGreatestBound5) tg ∧
    ∃ vg, !qqFvarDef vg g ∧ ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧ ∃ vx, !qqFvarDef vx x ∧ ∃ vy, !qqFvarDef vy y ∧
    ∃ v1, !adjoinDef v1 vy 0 ∧ ∃ v2, !adjoinDef v2 vx v1 ∧ ∃ v3, !adjoinDef v3 vb v2 ∧
    ∃ v4, !adjoinDef v4 va v3 ∧ ∃ vec, !adjoinDef vec vg v4 ∧
    ∃ bij, !(substsGraph SourceL) bij vec jb ∧ ∃ src, !(substsGraph SourceL) src vec sg ∧
    ∃ edg, !(substsGraph SourceL) edg vec ge ∧ ∃ dst, !(substsGraph SourceL) dst vec tg ∧
    ∃ ne, !(negGraph SourceL) ne edg ∧ ∃ imp3, !qqOrDef imp3 ne dst ∧
    ∃ ns, !(negGraph SourceL) ns src ∧ ∃ imp2, !qqOrDef imp2 ns imp3 ∧
    ∃ sp, !contextFiveGraph sp body vg va vb vx vy ctx du ∧ ∃ r1, !contextMPGraph r1 bij imp2 ctx sp dhb ∧
    ∃ r2, !contextMPGraph r2 src imp3 ctx r1 dhg ∧ !contextMPGraph out edg dst ctx r2 dhe”

theorem greatestImageAtGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 10 → M => greatestImageAtCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9)) greatestImageAtGraph := by
  haveI := contextFiveGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun w => by simp [greatestImageAtGraph,greatestImageAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def greatestImageAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (g a b x y : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ greatestImageBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dhb : T ⊢!ᵈᵉʳ insert ((⌜bijectionBound5⌝ : Semiformula M SourceL 5).subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) Γ)
    (dhg : T ⊢!ᵈᵉʳ insert ((⌜sourceGreatestBound5⌝ : Semiformula M SourceL 5).subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) Γ)
    (dhe : T ⊢!ᵈᵉʳ insert ((⌜graphEdgeBound5⌝ : Semiformula M SourceL 5).subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜targetGreatestBound5⌝ : Semiformula M SourceL 5).subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) Γ := by
  let body : Semiformula M SourceL 5 := ⌜greatestImageBound⌝
  let bij : Semiformula M SourceL 5 := ⌜bijectionBound5⌝
  let src : Semiformula M SourceL 5 := ⌜sourceGreatestBound5⌝
  let edg : Semiformula M SourceL 5 := ⌜graphEdgeBound5⌝
  let dst : Semiformula M SourceL 5 := ⌜targetGreatestBound5⌝
  have heb : body = bij 🡒 (src 🡒 (edg 🡒 dst)) := by
    simp [body,bij,src,edg,dst,greatestImageBound,bijectionBound5,sourceGreatestBound5,graphEdgeBound5,targetGreatestBound5,sourceImply, ←Semiformula.neg_eq, Bootstrapping.Semiformula.imp_def]
  have heu : (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ greatestImageBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ body := by simp [body]
  let du' := TDerivation.cast (congrArg (fun q => insert q Γ) heu) du
  let sp := contextFiveProof T Γ body (Semiterm.fvar g) (Semiterm.fvar a) (Semiterm.fvar b) (Semiterm.fvar x) (Semiterm.fvar y) du'
  have hei : (body.subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y] : Formula M SourceL) =
      ((bij.subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) 🡒
       ((src.subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) 🡒
       ((edg.subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) 🡒
         (dst.subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y])))) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun q => insert q Γ) hei) sp
  let r1 := contextMPProof T Γ _ _ sp' dhb
  let r2 := contextMPProof T Γ _ _ r1 dhg
  exact contextMPProof T Γ _ _ r2 dhe

@[simp] theorem greatestImageAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (g a b x y : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ greatestImageBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (dhb : T ⊢!ᵈᵉʳ insert ((⌜bijectionBound5⌝ : Semiformula M SourceL 5).subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) Γ)
    (dhg : T ⊢!ᵈᵉʳ insert ((⌜sourceGreatestBound5⌝ : Semiformula M SourceL 5).subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) Γ)
    (dhe : T ⊢!ᵈᵉʳ insert ((⌜graphEdgeBound5⌝ : Semiformula M SourceL 5).subst ![Semiterm.fvar g,Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar x,Semiterm.fvar y]) Γ) :
    (greatestImageAtProof T Γ g a b x y du dhb dhg dhe).val = greatestImageAtCode g a b x y Γ.val du.val dhb.val dhg.val dhe.val := by
  simp [greatestImageAtProof,greatestImageAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms greatestImageAtProof_val
#print axioms greatestImageAtGraph_defined
#print axioms greatestImageAtProof
end models
end PA194GreatestImageAtCode
