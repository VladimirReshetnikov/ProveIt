module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedBudgetBounds
public import M6PA.Calibration.ActualFixedCertificateExistence
public import M6PA.Calibration.NumericPAeqFormulaClosedQuote
@[expose] public section

/-! One genuinely supplied standard native certificate seed for each of the
fixed twelve typed PAeq images. Allocator/reserve relocation is separate. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Ordinal (Term Formula)
open PairGraph

def fixedImageReserve (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) : Nat :=
  functionBudgetBound 1 + commutativityBudgetBound 1 +
  (1+lkBudget addCommutativityDerivation) +
  (1+6+depth (∼inverseProperty 0 (1+1))) +
  (1+2+lkBudget (inverseSymmetryDerivation 1 0)) +
  (1+lkBudget (interpretedFixedDerivation p hp (fun _ => .fvar 0))) +
  (1+Encodable.encode (formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0))))
theorem fixedImageReserve_code_bound (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    1+Encodable.encode (formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0)))≤fixedImageReserve p hp := by
  unfold fixedImageReserve
  omega

def fixedImageNativeCode (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) : Nat :=
  code (formula p Fin.elim0 (fun _ => .fvar 0)) (fun _ => 0) 1 (fixedImageReserve p hp)
def fixedImageNativeProof (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    NativeCalculus.ActualBasis.Proof (fixedImageNativeCode p hp) := by
  let z := fixedImageReserve p hp
  have hz : functionBudgetBound 1 + commutativityBudgetBound 1 +
      (1+lkBudget addCommutativityDerivation) +
      (1+6+depth (∼inverseProperty 0 (1+1))) +
      (1+2+lkBudget (inverseSymmetryDerivation 1 0)) +
      (1+lkBudget (interpretedFixedDerivation p hp (fun _ => .fvar 0))) +
  (1+Encodable.encode (formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0)))) ≤ z := Nat.le_refl _
  exact interpretedFixedSupplier p hp (fun _ => .fvar 0) (fun _ => 0) 1 z
    (FunctionCongruenceBudgets.of_bound _ _ _ (by decide) (by intro; decide) (by omega))
    (AdditionCommutativityBudget.of_bound _ _ _ (by decide) (by intro; decide) (by omega))
    (by omega) (by omega) (by omega) (by omega)

theorem pa_proves_fixedImageCertificate (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    theory ⊢ ActualFixedCertificateExistence.sentence (fixedImageNativeCode p hp) :=
  ActualFixedCertificateExistence.pa_proves_fixed (fixedImageNativeProof p hp)

#print axioms fixedImageReserve_code_bound
#print axioms fixedImageNativeProof
#print axioms pa_proves_fixedImageCertificate
end M6.PA.ForwardRelational

