import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicImproperInputProperness
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicZeroIdentification
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaLogarithm

/-!
# Input properness of the original Gamma name at positive rationals

Two encodings of the same positive rational parameter can use different
denominators, disk radii, and real lower certificates. The properness
theorem for the original order-zero Euler integrals transports the
original Gamma programs through all three changes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPositiveRationalProperness

open_ipra
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEulerLogarithmicZeroIdentification (original_logarithmic_order_zero_is_Gamma)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian)
open GaussianStirlingGammaLogarithm (arg euler_real_source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "GF" => GaussianGammaReciprocalInverse.gammaF
local notation "GD" => GaussianGammaReciprocalInverse.gammaData
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "ID" => GaussianEulerLogarithmicImproperName.data

theorem original_cross (z R B A a b : PTm n) (hz : Γ ⊢[PRAAx] source z R B A)
    (ha : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b)
    (same : Γ ⊢[PRAAx] ofGaussian z B ≐ fraction a b) :
    Γ ⊢[PRAAx] crossEquivalent GF GF (GD z R B A) (GaussianStirlingGammaLogarithm.gammaData a b) := by
  have hs : Γ ⊢[PRAAx] source (arg a) a b b :=
    .andI (euler_real_source a b ha).andE₁ ha.andE₁
  have transport := GaussianEulerLogarithmicImproperInputProperness.original_improper_proper
    zero z (arg a) R a B b A b (.andI hz.andE₁ (.andI hs.andE₁ same))
  exact cross_trans GF IF GF _ (ID zero z R B A) _
    (cross_symm _ _ _ _ (original_logarithmic_order_zero_is_Gamma _ _ _ _ hz))
    (cross_trans IF IF GF _ (ID zero (arg a) a b b) _ transport
      (original_logarithmic_order_zero_is_Gamma _ _ _ _ hs))

theorem actual_original_gamma_positive_rational_input_proper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((source (var 0) (var 1) (var 2) (var 3) ⋏
        (GaussianStirlingGammaLogarithm.source (var 4) (var 5) ⋏
          ofGaussian (var 0) (var 2) ≐ fraction (var 4) (var 5))) ⟶
        crossEquivalent GF GF (GD (var 0) (var 1) (var 2) (var 3))
          (GaussianStirlingGammaLogarithm.gammaData (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_cross _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaPositiveRationalProperness
