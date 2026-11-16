module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedBudgetBounds
public import PA196.Arithmetic.Fixed.Existence
public import M6PA.Calibration.NumericPAeqFormulaClosedQuote
public import PA196.Arithmetic.Certificates.Interface
public import PA196.Logic.Relational.SourceCode
public import PA196.Logic.Relational.Suppliers.PAInterpretedFixedSupplier
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.ForwardRelational


/-! One genuinely supplied standard native certificate seed for each of the
fixed twelve typed PAeq images. Allocator/reserve relocation is separate. -/
namespace PA196.Arithmetic.Transport.ForwardRelational
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
  PA196.Logic.Relational.Source.code (formula p Fin.elim0 (fun _ => .fvar 0)) (fun _ => 0) 1 (fixedImageReserve p hp)
def fixedImageNativeProof (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    PA196.Logic.Derivation (fixedImageNativeCode p hp) := by
  let z := fixedImageReserve p hp
  have hz : functionBudgetBound 1 + commutativityBudgetBound 1 +
      (1+lkBudget addCommutativityDerivation) +
      (1+6+depth (∼inverseProperty 0 (1+1))) +
      (1+2+lkBudget (inverseSymmetryDerivation 1 0)) +
      (1+lkBudget (interpretedFixedDerivation p hp (fun _ => .fvar 0))) +
  (1+Encodable.encode (formula p Fin.elim0 (fun _ => (.fvar 0 : Term 0)))) ≤ z := Nat.le_refl _
  exact PA196.Logic.Relational.ForwardRelational.interpretedFixedSupplier p hp (fun _ => .fvar 0) (fun _ => 0) 1 z
    (FunctionCongruenceBudgets.of_bound _ _ _ (by decide) (by intro; decide) (by omega))
    (AdditionCommutativityBudget.of_bound _ _ _ (by decide) (by intro; decide) (by omega))
    (by omega) (by omega) (by omega) (by omega)

theorem pa_proves_fixedImageCertificate (p : SourceFormula 0) (hp : p∈Presentation.fixedAxioms) :
    theory ⊢ PA196.Arithmetic.Fixed.sentence (fixedImageNativeCode p hp) :=
  PA196.Arithmetic.Fixed.pa_proves_fixed (fixedImageNativeProof p hp)

#print axioms fixedImageReserve_code_bound
#print axioms fixedImageNativeProof
#print axioms pa_proves_fixedImageCertificate
end PA196.Arithmetic.Transport.ForwardRelational

