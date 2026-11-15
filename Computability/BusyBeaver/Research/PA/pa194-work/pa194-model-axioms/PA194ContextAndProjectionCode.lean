import PA194ContextModusPonensCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ContextAndProjectionCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode
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

/-- First projection of a contextual conjunction, as an explicit proof code. -/
noncomputable def contextAndLeftCode (p q g d : M) : M :=
  let both := p ^⋏ q
  let target := insert p g
  let np := neg SourceL p
  let nq := neg SourceL q
  let negContext := insert (np ^⋎ nq) target
  let en := axL (insert np (insert nq negContext)) p
  let dn := orIntro negContext np nq en
  let wi := wkRule (insert both target) d
  cutRule target both wi dn

noncomputable def contextAndLeftGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out p q g d. ∃ both, !qqAndDef both p q ∧ ∃ target, !insertDef target p g ∧
    ∃ np, !(negGraph SourceL) np p ∧ ∃ nq, !(negGraph SourceL) nq q ∧
    ∃ disj, !qqOrDef disj np nq ∧ ∃ nc, !insertDef nc disj target ∧
    ∃ nqc, !insertDef nqc nq nc ∧ ∃ nps, !insertDef nps np nqc ∧
    ∃ en, !axLGraph en nps p ∧ ∃ dn, !orIntroGraph dn nc np nq en ∧
    ∃ bt, !insertDef bt both target ∧ ∃ wi, !wkRuleGraph wi bt d ∧
    !cutRuleGraph out target both wi dn”

theorem contextAndLeftGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => contextAndLeftCode (v 0) (v 1) (v 2) (v 3)) contextAndLeftGraph := by
  exact .mk fun v => by simp [contextAndLeftGraph,contextAndLeftCode]

noncomputable def contextAndLeftProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (d : T ⊢!ᵈᵉʳ insert (p ⋏ q) Γ) :
    T ⊢!ᵈᵉʳ insert p Γ := by
  let target := insert p Γ
  let nc := insert (∼p ⋎ ∼q) target
  let en : T ⊢!ᵈᵉʳ insert (∼p) (insert (∼q) nc) :=
    TDerivation.em p (by simp [nc,target]) (by simp)
  let dn : T ⊢!ᵈᵉʳ nc := TDerivation.or' (by simp [nc]) en
  let wi : T ⊢!ᵈᵉʳ insert (p ⋏ q) target :=
    TDerivation.wk d (by intro x hx; simp [target] at hx ⊢; tauto)
  have hdn : DerivationOf T.theory dn.val (insert (neg SourceL (p ⋏ q).val) target.val) := by
    have h := dn.derivationOf
    simpa [nc,DeMorgan.and] using h
  have hcut : Derivation T.theory (cutRule target.val (p ⋏ q).val wi.val dn.val) :=
    Derivation.cutRule wi.derivationOf hdn
  refine ⟨contextAndLeftCode p.val q.val Γ.val d.val, ?_⟩
  have he : contextAndLeftCode p.val q.val Γ.val d.val = cutRule target.val (p ⋏ q).val wi.val dn.val := by
    simp [contextAndLeftCode,target,nc,en,dn,wi]
  constructor
  · simp [contextAndLeftCode]
  · rw [he]; exact hcut

@[simp] theorem contextAndLeftProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (d : T ⊢!ᵈᵉʳ insert (p ⋏ q) Γ) :
    (contextAndLeftProof T Γ p q d).val = contextAndLeftCode p.val q.val Γ.val d.val := rfl

/-- Second projection of a contextual conjunction, as an explicit proof code. -/
noncomputable def contextAndRightCode (p q g d : M) : M :=
  let both := p ^⋏ q
  let target := insert q g
  let np := neg SourceL p
  let nq := neg SourceL q
  let negContext := insert (np ^⋎ nq) target
  let en := axL (insert np (insert nq negContext)) q
  let dn := orIntro negContext np nq en
  let wi := wkRule (insert both target) d
  cutRule target both wi dn

noncomputable def contextAndRightGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out p q g d. ∃ both, !qqAndDef both p q ∧ ∃ target, !insertDef target q g ∧
    ∃ np, !(negGraph SourceL) np p ∧ ∃ nq, !(negGraph SourceL) nq q ∧
    ∃ disj, !qqOrDef disj np nq ∧ ∃ nc, !insertDef nc disj target ∧
    ∃ nqc, !insertDef nqc nq nc ∧ ∃ nps, !insertDef nps np nqc ∧
    ∃ en, !axLGraph en nps q ∧ ∃ dn, !orIntroGraph dn nc np nq en ∧
    ∃ bt, !insertDef bt both target ∧ ∃ wi, !wkRuleGraph wi bt d ∧
    !cutRuleGraph out target both wi dn”

theorem contextAndRightGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => contextAndRightCode (v 0) (v 1) (v 2) (v 3)) contextAndRightGraph := by
  exact .mk fun v => by simp [contextAndRightGraph,contextAndRightCode]

noncomputable def contextAndRightProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (d : T ⊢!ᵈᵉʳ insert (p ⋏ q) Γ) :
    T ⊢!ᵈᵉʳ insert q Γ := by
  let target := insert q Γ
  let nc := insert (∼p ⋎ ∼q) target
  let en : T ⊢!ᵈᵉʳ insert (∼p) (insert (∼q) nc) :=
    TDerivation.em q (by simp [nc,target]) (by simp)
  let dn : T ⊢!ᵈᵉʳ nc := TDerivation.or' (by simp [nc]) en
  let wi : T ⊢!ᵈᵉʳ insert (p ⋏ q) target :=
    TDerivation.wk d (by intro x hx; simp [target] at hx ⊢; tauto)
  have hdn : DerivationOf T.theory dn.val (insert (neg SourceL (p ⋏ q).val) target.val) := by
    have h := dn.derivationOf
    simpa [nc,DeMorgan.and] using h
  have hcut : Derivation T.theory (cutRule target.val (p ⋏ q).val wi.val dn.val) :=
    Derivation.cutRule wi.derivationOf hdn
  refine ⟨contextAndRightCode p.val q.val Γ.val d.val, ?_⟩
  have he : contextAndRightCode p.val q.val Γ.val d.val = cutRule target.val (p ⋏ q).val wi.val dn.val := by
    simp [contextAndRightCode,target,nc,en,dn,wi]
  constructor
  · simp [contextAndRightCode]
  · rw [he]; exact hcut

@[simp] theorem contextAndRightProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p q : Formula M SourceL) (d : T ⊢!ᵈᵉʳ insert (p ⋏ q) Γ) :
    (contextAndRightProof T Γ p q d).val = contextAndRightCode p.val q.val Γ.val d.val := rfl

#print axioms contextAndRightGraph_defined
#print axioms contextAndRightProof
#print axioms contextAndRightProof_val
#print axioms contextAndLeftGraph_defined
#print axioms contextAndLeftProof
#print axioms contextAndLeftProof_val
end models
end PA194ContextAndProjectionCode
