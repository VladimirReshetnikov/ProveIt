import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoGuardAt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextAllCode PA194FixedSyntaxQuote PA194IsoGuardProperty PA194TraceDirectSyntax PA194TracePropertyCompose PA194SeparationTraceOpen PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- Substituting the outer ordinal leaves P's inner bound variable intact. -/
theorem isoGuardAt_expanded (p a : M) (hp : IsSemiformula SourceL 1 p) :
    (⟨isoGuardProperty p,by simpa using isoGuardProperty_scoped p hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a] =
      ∀⁰ ((∼((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 0,Semiterm.fvar a])) ⋎
        (⟨p,by simpa using hp⟩ : Semiformula M SourceL 1)) := by
  let P : Semiformula M SourceL 1 := ⟨p,by simpa using hp⟩
  let P2 : Semiformula M SourceL 2 := P.subst ![Semiterm.bvar 0]
  let G : Semiformula M SourceL 2 := ⌜isoGuardTemplate⌝
  have hP2 : P2.val = p := by
    have h := congrArg Semiformula.val (Semiformula.subst_eq_self₁ P)
    change subst SourceL (?[ ^#(0 : M)] : M) p = p at h
    change subst SourceL (?[ ^#(0 : M)] : M) p = p
    exact h
  have hQ : (⟨isoGuardProperty p,by simpa using isoGuardProperty_scoped p hp⟩ : Semiformula M SourceL 1) = ∀⁰ (∼G ⋎ P2) := by
    apply Semiformula.ext
    simp [isoGuardProperty,G,hP2,← Semiformula.quote_def]
  rw [hQ]
  simp only [Semiformula.substs_all,Semiformula.substs_or,Semiformula.substs_neg]
  have hv : SemitermVec.q (![Semiterm.fvar a] : SemitermVec M SourceL 1 0) =
      (![Semiterm.bvar 0,Semiterm.fvar a] : SemitermVec M SourceL 2 1) := by
    funext i
    fin_cases i <;> simp [SemitermVec.q]
  rw [hv]
  have hP : P2.subst ![Semiterm.bvar 0,Semiterm.fvar a] = P := by
    dsimp [P2]
    rw [Semiformula.substs_substs]
    simpa using Semiformula.subst_eq_self₁ P
  rw [hP]

/-- Contextual application of Q at an arbitrary model-valued index. -/
noncomputable def isoGuardAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p a b : M) (hp : IsSemiformula SourceL 1 p)
    (dq : T ⊢!ᵈᵉʳ insert
      ((⟨isoGuardProperty p, by simpa using isoGuardProperty_scoped p hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert
      ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨p,by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ := by
  let P : Semiformula M SourceL 1 := ⟨p,by simpa using hp⟩
  let G : Semiformula M SourceL 2 := ⌜isoGuardTemplate⌝
  let body : Semiformula M SourceL 1 := ∼(G.subst ![Semiterm.bvar 0,Semiterm.fvar a]) ⋎ P
  let guard : Formula M SourceL := G.subst ![Semiterm.fvar b,Semiterm.fvar a]
  let prop : Formula M SourceL := P.subst ![Semiterm.fvar b]
  have hdq : T ⊢!ᵈᵉʳ insert (∀⁰ body) Γ :=
    TDerivation.cast (congrArg (fun x => insert x Γ) (isoGuardAt_expanded p a hp)) dq
  let ds := contextSpecializeProof T Γ body (Semiterm.fvar b) hdq
  have hi : body.subst ![Semiterm.fvar b] = guard 🡒 prop := by
    dsimp only [body,guard,prop]
    simp [Semiformula.substs_substs, Semiformula.imp_def, Matrix.cons_val]
  let di := TDerivation.cast (congrArg (fun x => insert x Γ) hi) ds
  exact contextMPProof T Γ guard prop di dg

noncomputable def isoGuardBodyCode (p a : M) : M :=
  neg SourceL (subst SourceL (?[ ^#(0 : M), ^&a]) (⌜isoGuardTemplate⌝ : M)) ^⋎ p

noncomputable def isoGuardAtCode (p a b g dq dg : M) : M :=
  let body := isoGuardBodyCode p a
  let db := contextSpecializeCode body (^&b) g dq
  let guard := subst SourceL (?[ ^&b, ^&a]) (⌜isoGuardTemplate⌝ : M)
  let prop := substs1 SourceL (^&b) p
  contextMPCode guard prop g db dg

noncomputable def isoGuardAtGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out p a b g dq dg. ∃ tmpl, !(fixedFormulaQuoteGraph isoGuardTemplate) tmpl ∧
    ∃ zero, !qqBvarDef zero 0 ∧ ∃ ta, !qqFvarDef ta a ∧ ∃ tb, !qqFvarDef tb b ∧
    ∃ va, !adjoinDef va ta 0 ∧ ∃ vo, !adjoinDef vo zero va ∧
    ∃ gu, !(substsGraph SourceL) gu vo tmpl ∧ ∃ ng, !(negGraph SourceL) ng gu ∧
    ∃ body, !qqOrDef body ng p ∧ ∃ db, !contextSpecializeGraph db body tb g dq ∧
    ∃ vb, !adjoinDef vb tb va ∧ ∃ guard, !(substsGraph SourceL) guard vb tmpl ∧
    ∃ prop, !(substs1Graph SourceL) prop tb p ∧ !contextMPGraph out guard prop g db dg”

theorem isoGuardAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => isoGuardAtCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) isoGuardAtGraph := by
  haveI := contextSpecializeGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [isoGuardAtGraph,isoGuardAtCode,isoGuardBodyCode,fixedFormulaQuoteGraph_correct,substs1]

@[simp] theorem isoGuardAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p a b : M) (hp : IsSemiformula SourceL 1 p)
    (dq : T ⊢!ᵈᵉʳ insert
      ((⟨isoGuardProperty p, by simpa using isoGuardProperty_scoped p hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (dg : T ⊢!ᵈᵉʳ insert
      ((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    (isoGuardAtProof T Γ p a b hp dq dg).val = isoGuardAtCode p a b Γ.val dq.val dg.val := by
  simp [isoGuardAtProof, isoGuardAtCode, isoGuardBodyCode, Semiformula.quote_def,
    SemitermVec.val_succ, substs1]

/-- Universal introduction of Q(a), from its opened body in the shifted context. -/
noncomputable def isoGuardIntroProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p a : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert
      ((∼((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 0,Semiterm.fvar a]) ⋎
       (⟨p,by simpa using hp⟩ : Semiformula M SourceL 1)).free) Γ.shift) :
    T ⊢!ᵈᵉʳ insert
      ((⟨isoGuardProperty p, by simpa using isoGuardProperty_scoped p hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ := by
  let body : Semiformula M SourceL 1 := ∼((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 0,Semiterm.fvar a]) ⋎
       (⟨p,by simpa using hp⟩ : Semiformula M SourceL 1)
  let d' := contextAllProof T Γ body d
  exact TDerivation.cast (congrArg (fun x => insert x Γ) (isoGuardAt_expanded p a hp).symm) d'

noncomputable def isoGuardIntroCode (p a g d : M) : M :=
  contextAllCode (isoGuardBodyCode p a) g d

noncomputable def isoGuardIntroGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out p a g d. ∃ tmpl, !(fixedFormulaQuoteGraph isoGuardTemplate) tmpl ∧
    ∃ zero, !qqBvarDef zero 0 ∧ ∃ ta, !qqFvarDef ta a ∧
    ∃ va, !adjoinDef va ta 0 ∧ ∃ vo, !adjoinDef vo zero va ∧
    ∃ gu, !(substsGraph SourceL) gu vo tmpl ∧ ∃ ng, !(negGraph SourceL) ng gu ∧
    ∃ body, !qqOrDef body ng p ∧ !contextAllGraph out body g d”

theorem isoGuardIntroGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => isoGuardIntroCode (v 0) (v 1) (v 2) (v 3)) isoGuardIntroGraph := by
  haveI := contextAllGraph_defined (M := M)
  exact .mk fun v => by simp [isoGuardIntroGraph,isoGuardIntroCode,isoGuardBodyCode,fixedFormulaQuoteGraph_correct]

@[simp] theorem isoGuardIntroProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p a : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert
      ((∼((⌜isoGuardTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 0,Semiterm.fvar a]) ⋎
       (⟨p,by simpa using hp⟩ : Semiformula M SourceL 1)).free) Γ.shift) :
    (isoGuardIntroProof T Γ p a hp d).val = isoGuardIntroCode p a Γ.val d.val := by
  simp [isoGuardIntroProof,isoGuardIntroCode,isoGuardBodyCode,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms isoGuardIntroProof
#print axioms isoGuardIntroGraph_defined
#print axioms isoGuardIntroProof_val
#print axioms isoGuardAtGraph_defined
#print axioms isoGuardAtProof_val
#print axioms isoGuardAt_expanded
#print axioms isoGuardAtProof
end models
end PA194IsoGuardAt
