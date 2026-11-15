import PA194ContextBaseApplicationCode
import PA194InternalBaseAtContext
import PA194FixedSyntaxQuote
import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194OrdinalBaseApplicationCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194ContextBaseApplicationCode PA194FixedSyntaxQuote PA194InternalInductionBaseAt PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
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

noncomputable def ordinalBaseAtCode (p a g hb hd hz : M) : M :=
  contextBaseCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) (⌜zeroTemplate⌝ : M) p (^&a) g hb hd hz

noncomputable def ordinalBaseAtGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out p a g hb hd hz. ∃ dt, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dt ∧
    ∃ z, !(fixedFormulaQuoteGraph zeroTemplate) z ∧ ∃ t, !qqFvarDef t a ∧
      !contextBaseGraph out dt z p t g hb hd hz”

theorem ordinalBaseAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => ordinalBaseAtCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) ordinalBaseAtGraph := by
  haveI := contextBaseGraph_defined (M := M)
  exact .mk fun v => by simp [ordinalBaseAtGraph, ordinalBaseAtCode, fixedFormulaQuoteGraph_correct]

noncomputable def ordinalBaseAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a : M)
    (hp : IsSemiformula SourceL 1 p)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hz : T ⊢!ᵈᵉʳ insert ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ) :
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
  let hb' : T ⊢!ᵈᵉʳ insert (∀⁰ ((dom ⋏ zero) 🡒 prop)) Γ := TDerivation.cast (congrArg (fun q => insert q Γ) he) hb
  exact contextBaseProof T Γ dom zero prop (Semiterm.fvar a) hb' hd hz

@[simp] theorem ordinalBaseAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (p a : M)
    (hp : IsSemiformula SourceL 1 p)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode p, inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp⟩ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hz : T ⊢!ᵈᵉʳ insert ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ) :
    (ordinalBaseAtProof T Γ p a hp hb hd hz).val = ordinalBaseAtCode p a Γ.val hb.val hd.val hz.val := by
  simp [ordinalBaseAtProof, ordinalBaseAtCode, Semiformula.quote_def]

#print axioms ordinalBaseAtGraph_defined
#print axioms ordinalBaseAtProof
#print axioms ordinalBaseAtProof_val
end models
end PA194OrdinalBaseApplicationCode
