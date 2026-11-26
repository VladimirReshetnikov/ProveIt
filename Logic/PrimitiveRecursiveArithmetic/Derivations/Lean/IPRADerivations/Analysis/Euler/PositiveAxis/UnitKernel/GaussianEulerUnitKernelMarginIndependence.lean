import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelCompactName
import IPRADerivations.Analysis.Integration.GaussianCompactMeshIndependence

/-!
# Original ordinary unit-panel names ignore the margin certificate

The native panel, evaluator and parameter datum remain unchanged. Two
independent genuine compact-margin guards supply their own original
Lipschitz and mesh budgets. The checked common-grid comparison identifies
both actual original names, including independently requested precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelMarginIndependence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitKernelCompactName (source nameF data evaluatorF fixedData lipschitz compact_input)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_margin_invariance (z R B a C E G J : PTm n)
    (hG : Γ ⊢[PRAAx] source z R B a C E G) (hJ : Γ ⊢[PRAAx] source z R B a C E J) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data z R B a C E G) (data z R B a C E J) :=
  GaussianCompactMeshIndependence.name_independence evaluatorF a C E (lipschitz R G) one
    (lipschitz R J) one (fixedData z B)
    (.andI (compact_input z R B a C E G hG) (compact_input z R B a C E J hJ))

theorem original_observations (p q z R B a C E G J : PTm n)
    (hG : Γ ⊢[PRAAx] source z R B a C E G) (hJ : Γ ⊢[PRAAx] source z R B a C E J) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C E G)) (ap2 nameF q (data z R B a C E J))
      (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_margin_invariance z R B a C E G J hG hJ)

theorem actual_original_unit_kernel_margin_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⋏
      source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7)) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7))) :=
  closeUniv 8 (.impI (original_margin_invariance _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_original_unit_kernel_independent_margin_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
      source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9)) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (ap2 nameF (var 1) (data (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 10 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelMarginIndependence
