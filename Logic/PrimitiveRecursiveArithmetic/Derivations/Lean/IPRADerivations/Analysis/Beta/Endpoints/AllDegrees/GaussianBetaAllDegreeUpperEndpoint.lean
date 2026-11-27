import IPRADerivations.Analysis.Beta.Endpoints.AllDegrees.GaussianBetaAllDegreeEulerInverse
import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperGridEndpoint

/-!
# Original upper grid comparison at every positive beta degree

The exact original scaled grid endpoint, its factor and its precision
are retained. The finite Euler reciprocal uses the same original producer
with the all-degree certificate computed from the actual beta endpoint.
The numerical error is unchanged, with independent observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeUpperEndpoint

open_ipra
open GaussianRationalMetric (distanceBounded)
open GaussianBetaUpperGridEndpoint (scaledEndpoint precision numerator sampled_endpoint_error_of_cross retime_endpoint_error)
open GaussianBetaAllDegreeEulerInverse (nameF data)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B A b N : PTm n) : Fm PTm n :=
  GaussianBetaAllDegreeEulerInverse.source z R B A N ⋏ le one b

theorem sampled_endpoint_error (p q z R B A b N : PTm n) (h : Γ ⊢[PRAAx] source z R B A b N) : Γ ⊢[PRAAx]
    distanceBounded (scaledEndpoint p z B b N) (ap2 nameF q (data z B N))
      (numerator p q z B b N) (unit p*unit q) :=
  sampled_endpoint_error_of_cross p q z B b N nameF (data z B N)
    (GaussianEulerIntegrandName.power_regular z B (b*N) b
      (GaussianBetaUpperEndpointName.power_source z B b N h.andE₁.andE₁.andE₂.andE₁.andE₁ h.andE₂ h.andE₁.andE₂))
    (GaussianBetaAllDegreeEulerInverse.original_upper_inverse z R B A b N h.andE₁ h.andE₂)

theorem upper_error_at (t p q z R B A b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A b N)
    (hp : Γ ⊢[PRAAx] le (precision t z B b N) p) :
    Γ ⊢[PRAAx] distanceBounded (scaledEndpoint p z B b N)
      (ap2 nameF q (data z B N)) (unit t+unit q) (unit t*unit q) :=
  retime_endpoint_error t p q z B b N _ hp (sampled_endpoint_error p q z R B A b N h)

theorem retimed_endpoint_error (t q z R B A b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A b N) :
    Γ ⊢[PRAAx] distanceBounded (scaledEndpoint (precision t z B b N) z B b N)
      (ap2 nameF q (data z B N)) (unit t+unit q) (unit t*unit q) :=
  upper_error_at t _ q z R B A b N h (le_refl _)

theorem all_degree_original_grid_upper_endpoint_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        distanceBounded (scaledEndpoint (var 0) (var 2) (var 4) (var 6) (var 7))
          (ap2 nameF (var 1) (data (var 2) (var 4) (var 7)))
          (numerator (var 0) (var 1) (var 2) (var 4) (var 6) (var 7)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (sampled_endpoint_error _ _ _ _ _ _ _ _ Prf.hyp0))

theorem all_degree_retimed_grid_upper_endpoint_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⋏
          le (precision (var 0) (var 3) (var 5) (var 7) (var 8)) (var 1)) ⟶
        distanceBounded (scaledEndpoint (var 1) (var 3) (var 5) (var 7) (var 8))
          (ap2 nameF (var 2) (data (var 3) (var 5) (var 8)))
          (unit (var 0)+unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 9 (.impI (upper_error_at _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeUpperEndpoint
