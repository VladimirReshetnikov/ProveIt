import PA194SourcePolarity
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
/-! Conditional model-internal preservation for the source universal rule.
The proof of the reopened-body premise from the original body remains open. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace PA194SourceAllPreservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194CanonicalDualForall PA194DualRecursion PA194DualQuantRecursion PA194DualAtomCode
  PA194TagDecoder PA194ChildCodes PA194SourceOutputWF PA194SourcePolarity
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem universal_code (label body : M) :
    π₁ (F fixedTranslation (fun _ => 4*cantor body label + 2)) =
      ^∀ (PA194InternalFormulaClose.close label 0 (π₁ (F fixedTranslation (fun _ => body)))) := by
  have ht : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) fixedTag :=
    (Classical.choose_spec PRA_has_tagCode).2
  have hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) fixedFirst :=
    (Classical.choose_spec PRA_has_firstChildCode).2
  have hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) fixedSecond :=
    (Classical.choose_spec PRA_has_secondChildCode).2
  have hw := fixed_all_wf body
  have h := translation_universal fixedTag fixedFirst fixedSecond ht hfirst hsecond label body hw.1 hw.2
  change F fixedTranslation (fun _ => 4*cantor body label+2) = _ at h
  rw [h,pi₁_pair]
  rfl

theorem all_of_free (label body : M)
    (hfree : Provable (𝗣𝗔 : ArithmeticTheory)
      (Bootstrapping.free ℒₒᵣ (PA194InternalFormulaClose.close label 0 (π₁ (F fixedTranslation (fun _ => body)))))) :
    Provable (𝗣𝗔 : ArithmeticTheory) (π₁ (F fixedTranslation (fun _ => 4*cantor body label+2))) := by
  have hp := (fixed_all_wf body).1
  let ψ : Bootstrapping.Semiformula M ℒₒᵣ 1 :=
    ⟨PA194InternalFormulaClose.close label 0 (π₁ (F fixedTranslation (fun _ => body))), by
      simpa using PA194InternalFormulaClose.close_wellformed label 0 _ hp⟩
  have hψ : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ψ.free := by
    apply (tprovable_iff_provable).mpr
    simpa [ψ] using hfree
  have hall : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ (∀⁰ ψ) := TProof.all! hψ
  rw [universal_code]
  change Provable (𝗣𝗔 : ArithmeticTheory) (∀⁰ ψ).val
  exact (tprovable_iff_provable).mp hall

#print axioms universal_code
#print axioms all_of_free
end models
end PA194SourceAllPreservation
