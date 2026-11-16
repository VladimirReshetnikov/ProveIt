import PA194InternalInductionBaseAt
import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalBaseAtContext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InternalInductionBaseAt PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
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

/-- Base application under an arbitrary internal one-sided sequent context. -/
noncomputable def baseAtTypedCtx (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (dom zero prop : Semiformula M SourceL 1) (t : Term M SourceL)
    (hbase : T ⊢!ᵈᵉʳ insert (∀⁰ ((dom ⋏ zero) 🡒 prop)) Γ)
    (hdom : T ⊢!ᵈᵉʳ insert (dom.subst ![t]) Γ) (hzero : T ⊢!ᵈᵉʳ insert (zero.subst ![t]) Γ) :
    T ⊢!ᵈᵉʳ insert (prop.subst ![t]) Γ := by
  have hi : T ⊢!ᵈᵉʳ insert ((dom.subst ![t] ⋏ zero.subst ![t]) 🡒 prop.subst ![t]) Γ := by
    simpa using TDerivation.specialize hbase t
  have hs : T ⊢!ᵈᵉʳ insert (dom.subst ![t] ⋏ zero.subst ![t]) Γ := TDerivation.and hdom hzero
  exact TDerivation.modusPonens hi hs

noncomputable def baseAtCtx (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a : M)
    (hp : IsSemiformula SourceL 1 p)
    (hbase : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hdom : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hzero : T ⊢!ᵈᵉʳ insert ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ := by
  let dom : Semiformula M SourceL 1 := ⌜PA194OrdinalBaseQuote.domainTemplate⌝
  let zero : Semiformula M SourceL 1 := ⌜zeroTemplate⌝
  let prop : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  have he : (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) = ∀⁰ ((dom ⋏ zero) 🡒 prop) := by
    apply Semiformula.ext
    simp [baseCode, inductionBaseCode, Semiformula.imp_def, dom, zero, prop]
    rw [neg_and (Semiformula.quote_isSemiformul₁ PA194OrdinalBaseQuote.domainTemplate).isUFormula
      (Semiformula.quote_isSemiformul₁ zeroTemplate).isUFormula]
    rfl
  have hb : T ⊢!ᵈᵉʳ insert (∀⁰ ((dom ⋏ zero) 🡒 prop)) Γ := by rw [← he]; exact hbase
  exact baseAtTypedCtx T Γ dom zero prop (Semiterm.fvar a) hb hdom hzero

#print axioms baseAtTypedCtx
#print axioms baseAtCtx
end models
end PA194InternalBaseAtContext
