import IPRADerivations.Analysis.GaussianBetaKernelRefinement

/-!
# The actual beta kernel is bounded by one on its full support

The SAME original normalized base is the genuine fraction (bN-a)/(bN).
Its native nonnegative numerator is at most the positive denominator.
The old actual finite power bound proves the original kernel norm bound,
including zero and the endpoint a=bN. No exponential reference or output
majorant is supplied as a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelUnitBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaKernelRefinement (source base_fraction)
open GaussianBetaKernelExponential (base kernel)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalReciprocal (bound_congr)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem base_bound (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx] bounded (base a b N) one one := by
  let D := b*N
  let A := monus D a
  have hd := positive_product b N h.andE₁ h.andE₂.andE₁
  have fraction : Γ ⊢[PRAAx] bounded (GaussianPositiveRationalLogarithm.fraction A D) A D :=
    bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point A D hd).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded A D hd)
  have unit : Γ ⊢[PRAAx] bounded (GaussianPositiveRationalLogarithm.fraction A D) one one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hd (le_refl _)
      (le_congr (by dsimp only [D,A]; ipra_ring) (by dsimp only [D,A]; ipra_ring) (GaussianRationalMonicReconstruction.monus_le_left D a)) fraction
  exact bound_congr (base_fraction a b N h).eqSymm (.eqRefl _) (.eqRefl _) unit

/-- Literal full-support beta power, at every internal degree. -/
theorem kernel_bound (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx] bounded (kernel a b N) one one :=
  bound_congr (.eqRefl _) (AnalyticNumberTheory.Order.pw_one_base N) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_power_integer (base a b N) one N (base_bound a b N h))

theorem original_beta_base_unit_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ bounded (base (var 0) (var 1) (var 2)) one one) :=
  closeUniv 3 (.impI (base_bound _ _ _ Prf.hyp0))
theorem original_full_support_beta_kernel_unit_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ bounded (kernel (var 0) (var 1) (var 2)) one one) :=
  closeUniv 3 (.impI (kernel_bound _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelUnitBound
