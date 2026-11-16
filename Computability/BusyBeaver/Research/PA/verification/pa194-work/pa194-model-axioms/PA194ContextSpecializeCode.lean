import PA194ContextModusPonensCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextSpecializeCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode
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

/-- Explicit one-binder specialization proof code under a shared context. -/
noncomputable def contextSpecializeCode (p t g d : M) : M :=
  let inst := substs1 SourceL t p
  let np := neg SourceL p
  let ninst := neg SourceL inst
  let all := ^∀ p
  let nex := ^∃ np
  let target := insert inst g
  let u := insert nex target
  let en := axL (insert ninst u) inst
  let ex := exsIntro u np t en
  let wd := wkRule (insert all target) d
  cutRule target all wd ex

noncomputable def contextSpecializeGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out p t g d. ∃ inst, !(substs1Graph SourceL) inst t p ∧ ∃ np, !(negGraph SourceL) np p ∧
    ∃ ni, !(negGraph SourceL) ni inst ∧ ∃ al, !qqAllDef al p ∧ ∃ ne, !qqExsDef ne np ∧
    ∃ target, !insertDef target inst g ∧ ∃ u, !insertDef u ne target ∧
    ∃ ns, !insertDef ns ni u ∧ ∃ en, !axLGraph en ns inst ∧ ∃ ex, !exsIntroGraph ex u np t en ∧
    ∃ as, !insertDef as al target ∧ ∃ wd, !wkRuleGraph wd as d ∧ !cutRuleGraph out target al wd ex”

theorem contextSpecializeGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => contextSpecializeCode (v 0) (v 1) (v 2) (v 3)) contextSpecializeGraph := .mk fun v => by
  simp [contextSpecializeGraph,contextSpecializeCode]

noncomputable def contextSpecializeProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 1) (t : Term M SourceL) (d : T ⊢!ᵈᵉʳ insert (∀⁰ p) Γ) :
    T ⊢!ᵈᵉʳ insert (p.subst ![t]) Γ := by
  let inst : Formula M SourceL := p.subst ![t]
  let np : Semiformula M SourceL 1 := ∼p
  let target : Sequent M SourceL := insert inst Γ
  let u : Sequent M SourceL := insert (∃⁰ np) target
  let en : T ⊢!ᵈᵉʳ insert (∼inst) u :=
    TDerivation.em inst (by simp [u,target]) (by simp)
  have hsub : substs1 SourceL t.val np.val = neg SourceL inst.val := by
    have hw : IsSemitermVec SourceL 1 0 (?[t.val] : M) := by
      simpa using (show (SemitermVec.val ![t]).isSemitermVec from (SemitermVec.isSemitermVec ![t]))
    have hp : IsSemiformula SourceL 1 p.val := by simpa using p.isSemiformula
    simpa [inst,np,substs1] using (substs_neg hp hw)
  have hen : DerivationOf T.theory en.val (insert (substs1 SourceL t.val np.val) u.val) := by
    rw [hsub]
    exact en.derivationOf
  have hex : Derivation T.theory (exsIntro u.val np.val t.val en.val) :=
    Derivation.exsIntro (by simp [u]) t.isSemiterm hen
  let wd : T ⊢!ᵈᵉʳ insert (∀⁰ p) target :=
    TDerivation.wk d (by intro x hx; simp [target] at hx ⊢; tauto)
  have hneg : DerivationOf T.theory (exsIntro u.val np.val t.val en.val)
      (insert (neg SourceL (∀⁰ p).val) target.val) := by
    constructor
    · simp [u,np,Bootstrapping.Semiformula.neg_all]
    · exact hex
  have hcut : Derivation T.theory (cutRule target.val (∀⁰ p).val wd.val (exsIntro u.val np.val t.val en.val)) :=
    Derivation.cutRule wd.derivationOf hneg
  refine ⟨contextSpecializeCode p.val t.val Γ.val d.val, ?_⟩
  have hcode : contextSpecializeCode p.val t.val Γ.val d.val =
      cutRule target.val (∀⁰ p).val wd.val (exsIntro u.val np.val t.val en.val) := by
    simp [contextSpecializeCode,inst,np,target,u,en,wd,substs1,SemitermVec.val_succ]
  constructor
  · simp [contextSpecializeCode, substs1]
  · rw [hcode]
    exact hcut

@[simp] theorem contextSpecializeProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p : Semiformula M SourceL 1) (t : Term M SourceL) (d : T ⊢!ᵈᵉʳ insert (∀⁰ p) Γ) :
    (contextSpecializeProof T Γ p t d).val = contextSpecializeCode p.val t.val Γ.val d.val := rfl

#print axioms contextSpecializeGraph_defined
#print axioms contextSpecializeProof
#print axioms contextSpecializeProof_val
end models
end PA194ContextSpecializeCode
