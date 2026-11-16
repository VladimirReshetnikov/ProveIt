import PA194ContextDoubleSpecializeCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextStepApplicationCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextDoubleSpecializeCode PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Explicit contextual proof code applying an arbitrary two-variable step. -/
noncomputable def contextStepCode (d1 d0 succ pred post t u g hs h1 h0 hr hp : M) : M :=
  let v := (?[t,u] : M)
  let i1 := subst SourceL v d1
  let i0 := subst SourceL v d0
  let ir := subst SourceL v succ
  let ip := subst SourceL v pred
  let iq := subst SourceL v post
  let pre := d1 ^⋏ (d0 ^⋏ (succ ^⋏ pred))
  let body := neg SourceL pre ^⋎ post
  let step := contextDoubleCode body t u g hs
  let rp := contextAndCode ir ip g hr hp
  let zr := contextAndCode i0 (ir ^⋏ ip) g h0 rp
  let one := contextAndCode i1 (i0 ^⋏ (ir ^⋏ ip)) g h1 zr
  contextMPCode (i1 ^⋏ (i0 ^⋏ (ir ^⋏ ip))) iq g step one

noncomputable def contextStepGraph : 𝚺₁.Semisentence 14 := .mkSigma
  “out d1 d0 succ pred post t u g hs h1 h0 hr hp.
    ∃ vu, !adjoinDef vu u 0 ∧ ∃ v, !adjoinDef v t vu ∧
    ∃ i1, !(substsGraph SourceL) i1 v d1 ∧ ∃ i0, !(substsGraph SourceL) i0 v d0 ∧
    ∃ ir, !(substsGraph SourceL) ir v succ ∧ ∃ ip, !(substsGraph SourceL) ip v pred ∧
    ∃ iq, !(substsGraph SourceL) iq v post ∧ ∃ rp0, !qqAndDef rp0 succ pred ∧
    ∃ zr0, !qqAndDef zr0 d0 rp0 ∧ ∃ pre, !qqAndDef pre d1 zr0 ∧
    ∃ np, !(negGraph SourceL) np pre ∧ ∃ body, !qqOrDef body np post ∧
    ∃ step, !contextDoubleGraph step body t u g hs ∧
    ∃ rp, !contextAndGraph rp ir ip g hr hp ∧ ∃ irip, !qqAndDef irip ir ip ∧
    ∃ zr, !contextAndGraph zr i0 irip g h0 rp ∧ ∃ i0irip, !qqAndDef i0irip i0 irip ∧
    ∃ one, !contextAndGraph one i1 i0irip g h1 zr ∧ ∃ all, !qqAndDef all i1 i0irip ∧
    !contextMPGraph out all iq g step one”

theorem contextStepGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 13 → M => contextStepCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11) (v 12)) contextStepGraph := by
  haveI := contextDoubleGraph_defined (M := M)
  haveI := contextAndGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [contextStepGraph,contextStepCode]

noncomputable def contextStepProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (d1 d0 succ pred post : Semiformula M SourceL 2) (t u : Term M SourceL)
    (hs : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ((d1 ⋏ (d0 ⋏ (succ ⋏ pred))) 🡒 post)) Γ)
    (h1 : T ⊢!ᵈᵉʳ insert (d1.subst ![t,u]) Γ) (h0 : T ⊢!ᵈᵉʳ insert (d0.subst ![t,u]) Γ)
    (hr : T ⊢!ᵈᵉʳ insert (succ.subst ![t,u]) Γ) (hp : T ⊢!ᵈᵉʳ insert (pred.subst ![t,u]) Γ) :
    T ⊢!ᵈᵉʳ insert (post.subst ![t,u]) Γ := by
  let body := ((d1 ⋏ (d0 ⋏ (succ ⋏ pred))) 🡒 post)
  let sp := contextDoubleProof T Γ body t u hs
  have he : body.subst ![t,u] = ((d1.subst ![t,u] ⋏ (d0.subst ![t,u] ⋏
      (succ.subst ![t,u] ⋏ pred.subst ![t,u]))) 🡒 post.subst ![t,u]) := by simp [body]
  let sp' := TDerivation.cast (congrArg (fun q => insert q Γ) he) sp
  let rp := contextAndProof T Γ (succ.subst ![t,u]) (pred.subst ![t,u]) hr hp
  let zr := contextAndProof T Γ (d0.subst ![t,u]) (succ.subst ![t,u] ⋏ pred.subst ![t,u]) h0 rp
  let one := contextAndProof T Γ (d1.subst ![t,u]) (d0.subst ![t,u] ⋏ (succ.subst ![t,u] ⋏ pred.subst ![t,u])) h1 zr
  exact contextMPProof T Γ _ _ sp' one

@[simp] theorem contextStepProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (d1 d0 succ pred post : Semiformula M SourceL 2) (t u : Term M SourceL)
    (hs : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ((d1 ⋏ (d0 ⋏ (succ ⋏ pred))) 🡒 post)) Γ)
    (h1 : T ⊢!ᵈᵉʳ insert (d1.subst ![t,u]) Γ) (h0 : T ⊢!ᵈᵉʳ insert (d0.subst ![t,u]) Γ)
    (hr : T ⊢!ᵈᵉʳ insert (succ.subst ![t,u]) Γ) (hp : T ⊢!ᵈᵉʳ insert (pred.subst ![t,u]) Γ) :
    (contextStepProof T Γ d1 d0 succ pred post t u hs h1 h0 hr hp).val =
      contextStepCode d1.val d0.val succ.val pred.val post.val t.val u.val Γ.val hs.val h1.val h0.val hr.val hp.val := by
  simp [contextStepProof,contextStepCode,Semiformula.imp_def,SemitermVec.val_succ]

#print axioms contextStepGraph_defined
#print axioms contextStepProof
#print axioms contextStepProof_val
end models
end PA194ContextStepApplicationCode
