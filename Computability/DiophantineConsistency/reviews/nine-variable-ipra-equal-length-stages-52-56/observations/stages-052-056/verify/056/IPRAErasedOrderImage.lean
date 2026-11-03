import DiophantineConsistency.IPRAErasedEqualityImages

/-! Preliminary syntactic form of the erased native order definition. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAErasedOrderImage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAErasedDefiningImages
open LO.Entailment

local instance : IPRAEqualityOnlyReference.language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (IPRAEqualityOnlyReference.EqualityRel k); infer_instance

def comparisonAtom : Semisentenceᵢ IPRAEqualityOnlyReference.language 2 :=
  Semiformulaᵢ.rel IPRAEqualityOnlyReference.EqualityRel.eq
    ![.func PRATheory.ltBitCode (fun i => .bvar i), .func PRALanguage.oneCode Fin.elim0]

theorem erase_orderDefinition :
    erase IPRANativeTheory.orderDefinitionI = ∀⁰* (comparisonAtom 🡘 comparisonAtom) := by
  have hv : (fun i : Fin 2 => Semiterm.lMap termsToReference
      ((![#0, #1] : Fin 2 → Semiterm PRALanguage.language Empty 2) i)) =
      (fun i => (#i : Semiterm IPRAEqualityOnlyReference.language Empty 2)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      rfl
  have hp : (fun i : Fin 2 => Semiterm.lMap termsToReference
      ((![.func PRATheory.ltBitCode (fun i => #i), .func PRALanguage.oneCode Fin.elim0] :
        Fin 2 → Semiterm PRALanguage.language Empty 2) i)) =
      ![.func PRATheory.ltBitCode (fun i => #i), .func PRALanguage.oneCode Fin.elim0] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Semiterm.lMap_func, termsToReference, Function.comp_def]
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      simp [Semiterm.lMap_func, termsToReference]
      funext k
      exact Fin.elim0 k
  simp [IPRANativeTheory.orderDefinitionI, erase_allClosure, erase, comparisonAtom,
    PRATheory.applyCode, hv, hp, LogicalConnective.iff]
  rfl

def order_image_provable :
    IPRAEqualityOnlyReference.referenceTheory ⊢! erase IPRANativeTheory.orderDefinitionI := by
  rw [erase_orderDefinition]
  apply Theoryᵢ.ofHilbert
  simp only [allClosure_succ, allClosure_zero, Rewriting.app_all]
  apply HilbertProofᵢ.gen
  simp only [Rewriting.app_all]
  apply HilbertProofᵢ.gen
  simp only [LogicalConnective.HomClass.map_iff]
  change (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language) ⊢! _
  exact E_Id

end DiophantineConsistency.IPRAErasedOrderImage
