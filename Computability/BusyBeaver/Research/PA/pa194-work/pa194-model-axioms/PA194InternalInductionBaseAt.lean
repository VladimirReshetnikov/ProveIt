import PA194InductionBaseShiftCode
import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalInductionBaseAt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
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

/-- Specialize the internal induction-base proof at any internal term. -/
noncomputable def baseAtTyped (T : InternalTheory M SourceL)
    (dom zero prop : Semiformula M SourceL 1) (t : Term M SourceL)
    (hbase : T ⊢! ∀⁰ ((dom ⋏ zero) 🡒 prop))
    (hdom : T ⊢! dom.subst ![t]) (hzero : T ⊢! zero.subst ![t]) :
    T ⊢! prop.subst ![t] := by
  have hi : T ⊢! (dom.subst ![t] ⋏ zero.subst ![t]) 🡒 prop.subst ![t] := by
    simpa using TProof.specialize hbase t
  have hs : T ⊢! dom.subst ![t] ⋏ zero.subst ![t] :=
    TDerivation.toTProof (TDerivation.and hdom hzero)
  exact TProof.modusPonens hi hs

/-- Apply the actual ordinal base to an arbitrary internal variable and property. -/
noncomputable def baseAtProof (T : InternalTheory M SourceL) (p a : M)
    (hp : IsSemiformula SourceL 1 p)
    (hbase : T ⊢! (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL))
    (hdom : T ⊢! (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])
    (hzero : T ⊢! (⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) :
    T ⊢! (⟨p, by simpa using hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a] := by
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
  have hb : T ⊢! ∀⁰ ((dom ⋏ zero) 🡒 prop) := he ▸ hbase
  exact baseAtTyped T dom zero prop (Semiterm.fvar a) hb hdom hzero

theorem baseAt_provable (T : InternalTheory M SourceL) (p a : M)
    (hp : IsSemiformula SourceL 1 p)
    (hb : Provable T.theory (baseCode p))
    (hd : Provable T.theory (substs1 SourceL (^&a) (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)))
    (hz : Provable T.theory (substs1 SourceL (^&a) (⌜zeroTemplate⌝ : M))) :
    Provable T.theory (substs1 SourceL (^&a) p) := by
  let b : Formula M SourceL := ⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩
  let f : Term M SourceL := Semiterm.fvar a
  let dom : Semiformula M SourceL 1 := ⌜PA194OrdinalBaseQuote.domainTemplate⌝
  let zero : Semiformula M SourceL 1 := ⌜zeroTemplate⌝
  let prop : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  have hbt : T ⊢! b := ((TProvable.iff_provable).2 hb).get
  have hdt : T ⊢! dom.subst ![f] := ((TProvable.iff_provable).2 (by simpa [dom,f,substs1,Semiformula.quote_def] using hd)).get
  have hzt : T ⊢! zero.subst ![f] := ((TProvable.iff_provable).2 (by simpa [zero,f,substs1,Semiformula.quote_def] using hz)).get
  have hout : T ⊢ prop.subst ![f] := ⟨baseAtProof T p a hp hbt hdt hzt⟩
  simpa [prop,f,substs1] using (TProvable.iff_provable).1 hout

#print axioms baseAt_provable
#print axioms baseAtProof
#print axioms baseAtTyped
end models
end PA194InternalInductionBaseAt
