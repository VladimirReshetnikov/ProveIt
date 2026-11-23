import IPRADerivations.Analysis.GaussianEulerUnitKernelVerticalSquare
import IPRADerivations.Analysis.GaussianEulerVerticalPointwise

/-!
# Source-only projected-real domination of the actual unit kernel

The unchanged complex unit kernel is bounded by its unchanged real-part
parameter comparator plus four ordinary observation tolerances. The
comparator's real samples are at least minus one observation tolerance;
the corrected radius is proved nonnegative from that actual lower bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelVerticalPointwise

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitKernelVerticalSquare (source kernel_source real_source original_kernel_square
  original_real_kernel_samples original_real_kernel_nonnegative)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianEulerUnitSubstitutionKernel (nameF data)
open GaussianEulerVerticalPointwise (corrected numerator corrected_positive corrected_represents)
open GaussianEulerVerticalRealRadius (denominator denominator_positive corrected_bounds_original)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianPositiveRadiusFiniteSum (boundBy)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Every parameter and time input is native. No norm or sign output
bound is supplied. Both original nested logarithm clocks are retained. -/
theorem original_named_bound (p z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    boundBy (ap2 nameF p (data z B a b)) (corrected (ap2 nameF p (data (argument z) B a b)) (unit p)) := by
  let q := ap2 nameF p (data (argument z) B a b)
  let U := unit p
  let S := GaussianEulerVerticalRealRadius.numerator q U
  let T := denominator q U
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have hT : Γ ⊢[PRAAx] le one T := denominator_positive q U hU
  have samples := original_real_kernel_samples z B a b h.andE₁.andE₁
  have real := GaussianSignedNameExponentialOrder.real_sample_at nameF (data (argument z) B a b) p samples
  have fixed := GaussianEulerVerticalRealSamples.real_input_fixed nameF p (data (argument z) B a b) samples
  have lower := original_real_kernel_nonnegative p z B a b h.andE₁.andE₁ h.andE₂
  have bound := corrected_bounds_original q U hU fixed lower
  have transferred := GaussianEulerVerticalNormTransfer.original_norm_transfer nameF nameF (data z B a b) (data (argument z) B a b) p S T hT
    (GaussianEulerUnitSubstitutionKernel.name_regular z B a b (kernel_source z R B a b h))
    (GaussianEulerUnitSubstitutionKernel.name_regular (argument z) B a b (kernel_source _ _ _ _ _ (real_source z R B a b h)))
    (original_kernel_square z R B a b h) bound
  have finalBound : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (ap2 nameF p (data z B a b)) (numerator q U) T :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hT hU) hT
      (le_of_eq_add (d := zero) (by dsimp only [S,T,numerator,GaussianEulerVerticalRealRadius.numerator,denominator]; ipra_ring)) transferred
  exact GaussianPositiveRadiusFiniteSum.from_representation _ _ _ _ hT (corrected_positive q U hU real.andE₂ lower)
    (corrected_represents q U hU lower) finalBound

theorem actual_original_unit_kernel_projected_real_domination_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      boundBy (ap2 nameF (var 0) (data (var 1) (var 3) (var 4) (var 5)))
        (corrected (ap2 nameF (var 0) (data (argument (var 1)) (var 3) (var 4) (var 5))) (unit (var 0)))) :=
  closeUniv 6 (.impI (original_named_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelVerticalPointwise
