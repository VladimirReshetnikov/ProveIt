import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayLowerEnvelope

/-!
# Actual original decay bounded below on every positive compact

All finite positive-exponential observations at a/b <= T lie between
one and 3^T. Their actual canonical reciprocals are at least 3^(-T).
The original independent negative exponential retains only its own
requested observation allowance after one finite scalar-gap removal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayCompactLower

open_ipra
open GaussianEulerIntegrandName (decayF decayData)
open GaussianEuclideanDistanceName (fraction)
open GaussianCoefficientNameBounds (unit)
open RationalValueBounds (upper)

alias finite_positive_envelope := GaussianEulerDecayLowerEnvelope.finite_positive_envelope
alias reciprocal_lower_of_positive_envelope := GaussianEulerDecayLowerEnvelope.reciprocal_lower_of_envelope
alias reciprocal_samples_lower := GaussianEulerDecayLowerEnvelope.compact_reciprocal_samples_lower
alias original_decay_lower := GaussianEulerDecayLowerEnvelope.compact_decay_lower

theorem actual_original_compact_decay_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 2) ⋏ le (var 1) (var 3*var 2)) ⟶
      upper (fraction one (pw (num 3) (var 3))) (fstT (ap2 decayF (var 0) (decayData (var 1) (var 2)))) one (unit (var 0))) :=
  closeUniv 4 (.impI (original_decay_lower _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayCompactLower
