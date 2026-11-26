import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelRationalTimeCleared
import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelSinhApartness
import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelZero
import IPRADerivations.Analysis.Names.GaussianNamedClearedScalarQuotient

/-!
# The actual elementary Binet kernel at rational time

For positive rational (t), the original cofinal kernel agrees with
`((t/2) cosh(t/2) − sinh(t/2)) / (t² sinh(t/2))`. This uses the actual
named reciprocal and a computed witness for the positive-time sinh.
At zero the original cofinal kernel has the existing value `1/12`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelElementaryRational

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelFrozenHyperbolic (fixedCoshF fixedCoshData fixed_cosh_regular fixedSinhF fixedSinhData fixed_sinh_regular)
open GaussianBinetKernelImaginaryRatioPrefix (timeSquare)
open GaussianBinetKernelRationalTimeCleared (leftF leftData halfTime)
open GaussianBinetKernelRows (inputData)
open GaussianBinetKernelSinhApartness (height sinh_apart)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianNameArithmetic (multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianNamedClearedScalarQuotient (quotientF quotientData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qone)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Kernel" => GaussianBinetKernelCofinal.nameF

def reciprocalSquare (A B : PTm n) : PTm n := fraction (B*B) (A*A)
def nameF : PR 2 := quotientF leftF fixedSinhF
def data (A B : PTm n) : PTm n :=
  quotientData leftF fixedSinhF (leftData A B) (fixedSinhData A B) (reciprocalSquare A B) (height A B)

theorem square_inverse (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (reciprocalSquare A B) (timeSquare A B) ≐ qone :=
  GaussianGammaHalfEulerSquare.inverse_fraction (B*B) (A*A) (positive_product _ _ hB hB) (positive_product _ _ hA hA)

theorem positive_equivalent (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent Kernel nameF (inputData A B) (data A B) := by
  have left := multiply_fast constantF fixedCoshF (halfTime A B) (fixedCoshData A B)
    (constant_regular _) (fixed_cosh_regular A B hB)
  have result := GaussianNamedClearedScalarQuotient.quotient_agrees leftF fixedSinhF Kernel
    (leftData A B) (fixedSinhData A B) (inputData A B) (timeSquare A B) (inputData A B)
    (reciprocalSquare A B) (height A B) left (fixed_sinh_regular A B hB) (GaussianBinetKernelCofinal.regular A B hB)
    (sinh_apart A B hA hB) (square_inverse A B hA hB) (GaussianBinetKernelRationalTimeCleared.cleared_kernel A B hB)
  exact cross_symm _ _ _ _ result

theorem actual_elementary_Binet_kernel_at_positive_rational_time_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((le one (var 0) ⋏ le one (var 1)) ⟶ crossEquivalent Kernel nameF (inputData (var 0) (var 1)) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (positive_equivalent _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_elementary_Binet_kernel_at_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ crossEquivalent Kernel constantF (inputData zero (var 0)) GaussianBinetKernelZero.endpoint) :=
  GaussianBinetKernelZero.actual_Binet_kernel_endpoint_closed

end LeanProofs.IPRA.Analysis.GaussianBinetKernelElementaryRational
