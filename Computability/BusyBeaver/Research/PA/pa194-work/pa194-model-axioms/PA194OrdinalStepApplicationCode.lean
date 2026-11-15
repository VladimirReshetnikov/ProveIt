import PA194ContextStepApplicationCode
import PA194FixedSyntaxQuote
import PA194InductionStepShiftCode
import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194OrdinalStepApplicationCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextStepApplicationCode PA194FixedSyntaxQuote PA194BindSource PA194InductionStepShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
open PA194OrdinalStepQuote PA194OrdinalStepFromProperty PA194InternalOrdinalStep
  PA194TypedSeparation
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

noncomputable def ordinalStepAtCode (p a b g hs h1 h0 hr hp : M) : M :=
  contextStepCode (⌜domainOne⌝ : M) (⌜domainZero⌝ : M) (⌜successorTemplate⌝ : M)
    (substs1 SourceL (^#(1 : M)) p) p (^&b) (^&a) g hs h1 h0 hr hp

noncomputable def ordinalStepAtGraph : 𝚺₁.Semisentence 10 := .mkSigma
  “out p a b g hs h1 h0 hr hp. ∃ d1, !(fixedFormulaQuoteGraph domainOne) d1 ∧
    ∃ d0, !(fixedFormulaQuoteGraph domainZero) d0 ∧ ∃ succ, !(fixedFormulaQuoteGraph successorTemplate) succ ∧
    ∃ one, !qqBvarDef one 1 ∧ ∃ pred, !(substs1Graph SourceL) pred one p ∧
    ∃ t, !qqFvarDef t b ∧ ∃ u, !qqFvarDef u a ∧
    !contextStepGraph out d1 d0 succ pred p t u g hs h1 h0 hr hp”

theorem ordinalStepAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 9 → M => ordinalStepAtCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8)) ordinalStepAtGraph := by
  haveI := contextStepGraph_defined (M := M)
  exact .mk fun v => by simp [ordinalStepAtGraph, ordinalStepAtCode, fixedFormulaQuoteGraph_correct]

noncomputable def ordinalStepAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a b : M)
    (hp : IsSemiformula SourceL 1 p)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (hd1 : T ⊢!ᵈᵉʳ insert ((⌜domainOne⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hd0 : T ⊢!ᵈᵉʳ insert ((⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hpred : T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ := by
  let prop : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  let d1 : Semiformula M SourceL 2 := ⌜domainOne⌝
  let d0 : Semiformula M SourceL 2 := ⌜domainZero⌝
  let succ : Semiformula M SourceL 2 := ⌜successorTemplate⌝
  let pred : Semiformula M SourceL 2 := prop.subst ![Semiterm.bvar 1]
  let post : Semiformula M SourceL 2 := prop.subst ![Semiterm.bvar 0]
  have hpost : post.val = p := by
    have h := congrArg Semiformula.val (Semiformula.subst_eq_self₁ prop)
    change subst SourceL (?[ ^#(0 : M)] : M) p = p at h
    change subst SourceL (?[ ^#(0 : M)] : M) p = p
    exact h
  have hpredval : pred.val = substs1 SourceL (^#(1 : M)) p := by
    simp [pred, prop, Bootstrapping.Semiformula.val_substs, substs1,
      SemitermVec.val_succ, Bootstrapping.Semiterm.bvar_val]
  have he : (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) =
      ∀⁰ ∀⁰ ((d1 ⋏ (d0 ⋏ (succ ⋏ pred))) 🡒 post) := by
    apply Semiformula.ext
    simp [stepCode, ordinalStepFromProperty, inductionStepCode, Semiformula.imp_def, d1, d0, succ, hpredval, hpost]
    have hv1 : IsUFormula SourceL (⌜domainOne⌝ : M) := (Semiformula.quote_isSemiformula domainOne).isUFormula
    have hv0 : IsUFormula SourceL (⌜domainZero⌝ : M) := (Semiformula.quote_isSemiformula domainZero).isUFormula
    have hvs : IsUFormula SourceL (⌜successorTemplate⌝ : M) := (Semiformula.quote_isSemiformula successorTemplate).isUFormula
    have hvp : IsUFormula SourceL (substs1 SourceL (^#(1 : M)) p) := by
      rw [← hpredval]
      exact pred.isSemiformula.isUFormula
    rw [neg_and hv1 (IsUFormula.and.mpr ⟨hv0, IsUFormula.and.mpr ⟨hvs,hvp⟩⟩),
      neg_and hv0 (IsUFormula.and.mpr ⟨hvs,hvp⟩), neg_and hvs hvp]
    rfl
  let hst : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ((d1 ⋏ (d0 ⋏ (succ ⋏ pred))) 🡒 post)) Γ :=
    TDerivation.cast (congrArg (fun q => insert q Γ) he) hstep
  have epred : (prop.subst ![Semiterm.fvar a] : Formula M SourceL) = pred.subst ![Semiterm.fvar b,Semiterm.fvar a] := by
    simp [pred, Semiformula.substs_substs]
  let hpred' := TDerivation.cast (congrArg (fun q => insert q Γ) epred) hpred
  let hout := contextStepProof T Γ d1 d0 succ pred post (Semiterm.fvar b) (Semiterm.fvar a) hst hd1 hd0 hs hpred'
  have epost : (post.subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) = prop.subst ![Semiterm.fvar b] := by
    simp [post, Semiformula.substs_substs]
  exact TDerivation.cast (congrArg (fun q => insert q Γ) epost) hout


@[simp] theorem ordinalStepAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a b : M)
    (hp : IsSemiformula SourceL 1 p)
    (hstep : T ⊢!ᵈᵉʳ insert (⟨stepCode p, stepCode_scoped p hp⟩ : Formula M SourceL) Γ)
    (hd1 : T ⊢!ᵈᵉʳ insert ((⌜domainOne⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hd0 : T ⊢!ᵈᵉʳ insert ((⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ)
    (hpred : T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ) :
    (ordinalStepAtProof T Γ p a b hp hstep hd1 hd0 hs hpred).val =
      ordinalStepAtCode p a b Γ.val hstep.val hd1.val hd0.val hs.val hpred.val := by
  have he := congrArg Semiformula.val (Semiformula.subst_eq_self₁ (⟨p, by simpa using hp⟩ : Semiformula M SourceL 1))
  change subst SourceL (?[ ^#(0 : M)] : M) p = p at he
  simp [ordinalStepAtProof, ordinalStepAtCode, Semiformula.quote_def, substs1, SemitermVec.val_succ, he]

#print axioms ordinalStepAtGraph_defined
#print axioms ordinalStepAtProof
#print axioms ordinalStepAtProof_val
end models
end PA194OrdinalStepApplicationCode
