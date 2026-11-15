import PA194InductionStepShiftCode
import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalStepAtContext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InductionStepShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
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

/-- Internal two-binder specialization under a shared one-sided context. -/
noncomputable def specializeTwoCtx (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (φ : Semiformula M SourceL 2) (t u : Term M SourceL)
    (h : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ φ) Γ) : T ⊢!ᵈᵉʳ insert (φ.subst ![t,u]) Γ := by
  have h1 : T ⊢!ᵈᵉʳ insert (∀⁰ Semiformula.subst (SemitermVec.q ![u]) φ) Γ := by
    simpa using TDerivation.specialize h u
  simpa [Semiformula.substs_substs] using TDerivation.specialize h1 t

/-- Apply a generic step instance while retaining an arbitrary internal context. -/
noncomputable def stepAtTypedCtx (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (domOne domZero succ pred post : Semiformula M SourceL 2) (t u : Term M SourceL)
    (hstep : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ((domOne ⋏ (domZero ⋏ (succ ⋏ pred))) 🡒 post)) Γ)
    (hd1 : T ⊢!ᵈᵉʳ insert (domOne.subst ![t,u]) Γ) (hd0 : T ⊢!ᵈᵉʳ insert (domZero.subst ![t,u]) Γ)
    (hs : T ⊢!ᵈᵉʳ insert (succ.subst ![t,u]) Γ) (hp : T ⊢!ᵈᵉʳ insert (pred.subst ![t,u]) Γ) :
    T ⊢!ᵈᵉʳ insert (post.subst ![t,u]) Γ := by
  have hi : T ⊢!ᵈᵉʳ insert ((domOne.subst ![t,u] ⋏ (domZero.subst ![t,u] ⋏
      (succ.subst ![t,u] ⋏ pred.subst ![t,u]))) 🡒 post.subst ![t,u]) Γ := by
    simpa using specializeTwoCtx T Γ _ t u hstep
  have hsp : T ⊢!ᵈᵉʳ insert (succ.subst ![t,u] ⋏ pred.subst ![t,u]) Γ := TDerivation.and hs hp
  have hz : T ⊢!ᵈᵉʳ insert (domZero.subst ![t,u] ⋏ (succ.subst ![t,u] ⋏ pred.subst ![t,u])) Γ := TDerivation.and hd0 hsp
  have hpre : T ⊢!ᵈᵉʳ insert (domOne.subst ![t,u] ⋏ (domZero.subst ![t,u] ⋏
      (succ.subst ![t,u] ⋏ pred.subst ![t,u]))) Γ := TDerivation.and hd1 hz
  exact TDerivation.modusPonens hi hpre

/-- Apply the actual ordinal step under a context at model-valued variables a and b. -/
noncomputable def stepAtCtx (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a b : M)
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
  have hst : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ((d1 ⋏ (d0 ⋏ (succ ⋏ pred))) 🡒 post)) Γ := by
    rw [← he]; exact hstep
  have hpred' : T ⊢!ᵈᵉʳ insert (pred.subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ := by
    simpa [pred, Semiformula.substs_substs] using hpred
  have hout := stepAtTypedCtx T Γ d1 d0 succ pred post (Semiterm.fvar b) (Semiterm.fvar a) hst hd1 hd0 hs hpred'
  simpa [post, Semiformula.substs_substs] using hout

#print axioms stepAtCtx
#print axioms specializeTwoCtx
#print axioms stepAtTypedCtx
end models
end PA194InternalStepAtContext
