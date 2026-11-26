import IPRADerivations.Analysis.Beta.Endpoints.AllDegrees.GaussianBetaAllDegreeInverseContinuity
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteMixedInputContinuity

/-!
# Different native encodings for the all-degree finite Euler input rate

Each rational input retains its own denominator, Q_N data, apartness
certificate and original reciprocal observation clock. Original native
right-half-plane sources and the input distance discharge the entire
rate statement; no computed output or Q_N rate is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeMixedInverseContinuity

open_ipra
open GaussianBetaAllDegreeInverseContinuity (source gain)
open GaussianBetaAllDegreeEulerInverse (nameF data)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (z w R B C A X Y N : PTm n) : Fm PTm n := source z w R B C A N ⋏
  (le one Y ⋏ distanceBounded (ofGaussian z B) (ofGaussian w C) X Y)
ipra_subst input

theorem original_independent_rate (z w R B C A X Y N : PTm n) (h : Γ ⊢[PRAAx] input z w R B C A X Y N) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data z B N) (data w C N) (gain R A N*X) Y := by
  have hz := h.andE₁.andE₁
  have hw := h.andE₁.andE₂
  have original := GaussianGammaFiniteMixedInputContinuity.original_mixed_independent_rate z w R B C X Y N
    hz.andE₂ hz.andE₁.andE₂.andE₁.andE₁ hw.andE₁.andE₂.andE₁.andE₁ h.andE₂.andE₁
    hz.andE₁.andE₂.andE₁.andE₂ hw.andE₁.andE₂.andE₁.andE₂ h.andE₂.andE₂
  exact GaussianBetaAllDegreeInverseContinuity.rate_congr nameF nameF _ _ _ _ _ _
    (by unfold gain; ipra_ring) (.eqRefl _)
    (GaussianBetaAllDegreeInverseContinuity.original_from_Q_rate z w R B C A N _ Y h.andE₁ h.andE₂.andE₁ original)

theorem original_observations (p q z w R B C A X Y N : PTm n) (h : Γ ⊢[PRAAx] input z w R B C A X Y N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z B N)) (ap2 nameF q (data w C N))
      (rateNumerator (gain R A N*X) Y p q) (rateDenominator Y p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_independent_rate z w R B C A X Y N h)

theorem original_all_degree_mixed_Euler_inverse_input_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      independentRate nameF nameF (data (var 0) (var 3) (var 8)) (data (var 1) (var 4) (var 8))
        (gain (var 2) (var 5) (var 8)*var 6) (var 7)) :=
  closeUniv 9 (.impI (original_independent_rate _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaAllDegreeMixedInverseContinuity
