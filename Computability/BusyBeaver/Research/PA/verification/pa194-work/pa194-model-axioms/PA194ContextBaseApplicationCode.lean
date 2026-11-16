import PA194ContextSpecializeCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextBaseApplicationCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Explicit code for specialization of a general base and two premise proofs. -/
noncomputable def contextBaseCode (dom zero prop t g hb hd hz : M) : M :=
  let body := neg SourceL (dom ^⋏ zero) ^⋎ prop
  let id := substs1 SourceL t dom
  let iz := substs1 SourceL t zero
  let ip := substs1 SourceL t prop
  let sp := contextSpecializeCode body t g hb
  let cp := contextAndCode id iz g hd hz
  contextMPCode (id ^⋏ iz) ip g sp cp

noncomputable def contextBaseGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “out dom zero prop t g hb hd hz. ∃ dz, !qqAndDef dz dom zero ∧ ∃ nd, !(negGraph SourceL) nd dz ∧
    ∃ body, !qqOrDef body nd prop ∧ ∃ id, !(substs1Graph SourceL) id t dom ∧
    ∃ iz, !(substs1Graph SourceL) iz t zero ∧ ∃ ip, !(substs1Graph SourceL) ip t prop ∧
    ∃ sp, !contextSpecializeGraph sp body t g hb ∧ ∃ cp, !contextAndGraph cp id iz g hd hz ∧
    ∃ cd, !qqAndDef cd id iz ∧ !contextMPGraph out cd ip g sp cp”

theorem contextBaseGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → M => contextBaseCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) contextBaseGraph := by
  haveI := contextSpecializeGraph_defined (M := M)
  haveI := contextAndGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [contextBaseGraph,contextBaseCode]

noncomputable def contextBaseProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (dom zero prop : Semiformula M SourceL 1) (t : Term M SourceL)
    (hb : T ⊢!ᵈᵉʳ insert (∀⁰ ((dom ⋏ zero) 🡒 prop)) Γ)
    (hd : T ⊢!ᵈᵉʳ insert (dom.subst ![t]) Γ) (hz : T ⊢!ᵈᵉʳ insert (zero.subst ![t]) Γ) :
    T ⊢!ᵈᵉʳ insert (prop.subst ![t]) Γ := by
  let body : Semiformula M SourceL 1 := (dom ⋏ zero) 🡒 prop
  let sp := contextSpecializeProof T Γ body t hb
  have he : body.subst ![t] = ((dom.subst ![t] ⋏ zero.subst ![t]) 🡒 prop.subst ![t]) := by simp [body]
  let sp' : T ⊢!ᵈᵉʳ insert ((dom.subst ![t] ⋏ zero.subst ![t]) 🡒 prop.subst ![t]) Γ :=
    TDerivation.cast (congrArg (fun q => insert q Γ) he) sp
  let cp := contextAndProof T Γ (dom.subst ![t]) (zero.subst ![t]) hd hz
  let out := contextMPProof T Γ (dom.subst ![t] ⋏ zero.subst ![t]) (prop.subst ![t]) sp' cp
  exact out

@[simp] theorem contextBaseProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (dom zero prop : Semiformula M SourceL 1) (t : Term M SourceL)
    (hb : T ⊢!ᵈᵉʳ insert (∀⁰ ((dom ⋏ zero) 🡒 prop)) Γ)
    (hd : T ⊢!ᵈᵉʳ insert (dom.subst ![t]) Γ) (hz : T ⊢!ᵈᵉʳ insert (zero.subst ![t]) Γ) :
    (contextBaseProof T Γ dom zero prop t hb hd hz).val =
      contextBaseCode dom.val zero.val prop.val t.val Γ.val hb.val hd.val hz.val := by
  simp [contextBaseProof,contextBaseCode,Semiformula.imp_def,substs1,SemitermVec.val_succ]

#print axioms contextBaseGraph_defined
#print axioms contextBaseProof
#print axioms contextBaseProof_val
end models
end PA194ContextBaseApplicationCode
