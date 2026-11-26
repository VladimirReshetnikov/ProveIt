import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerExponentCompactBounds
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialMajorant

/-!
# Uniform compact majorant for the original Euler power

The literal observations of t^(z-1) on [1/E,T] are bounded by
a single primitive recursive integer from the original input disk.
The bound is independent of the observation precision and of any
beta-kernel degree. The actual exponent query and actual series
cutoff are used in the finite exponential majorant.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactPowerMajorant

open_ipra
open GaussianEulerExponentCompactBounds (source)
open GaussianEulerIntegrandName (coefficient powerClock powerExponentF powerExponentData powerF powerData powerRadius)
open GaussianCompactLogarithmBounds (domain)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentRadius (R E T : PTm n) : PTm n := (R+one)*GaussianCompactLogarithmBounds.radius E T
def majorant (R E T : PTm n) : PTm n := pw (num 3) (exponentRadius R E T)

theorem exponent_sample (p z R B E T a b : PTm n) (hz : Γ ⊢[PRAAx] source z R B E)
    (ht : Γ ⊢[PRAAx] domain a b E T) :
    Γ ⊢[PRAAx] bounded (ap2 powerExponentF p (powerExponentData z B a b)) (exponentRadius R E T) one := by
  have c := GaussianEulerIntegrandName.coefficient_bound z R B hz.andE₁ hz.andE₂.andE₂
  have l := GaussianCompactLogarithmBounds.sample_bound (powerClock p z B a b) a b E T hz.andE₂.andE₁ ht
  exact bound_congr (GaussianEulerIntegrandName.power_exponent_at p z B a b).eqSymm
    (.eqRefl _) (by ipra_ring) (bounded_product _ _ _ _ _ _ (le_refl _) (le_refl _) c l)

theorem original_power_observation (p z R B E T a b : PTm n) (hz : Γ ⊢[PRAAx] source z R B E)
    (ht : Γ ⊢[PRAAx] domain a b E T) :
    Γ ⊢[PRAAx] bounded (ap2 powerF p (powerData z B a b)) (majorant R E T) one := by
  let r := powerRadius z B a b
  let j := GaussianRadiusExponentialName.inputPrecision r p
  let K := GaussianRadiusExponentialName.index r p
  have exp := GaussianPositiveExponentialMajorant.disk_bound
    (ap2 powerExponentF j (powerExponentData z B a b)) (exponentRadius R E T) K
      (exponent_sample j z R B E T a b hz ht)
  exact bound_congr (GaussianRadiusExponentialName.sample_at powerExponentF r p (powerExponentData z B a b)).eqSymm
    (.eqRefl _) (.eqRefl _) exp

theorem original_Euler_power_uniform_compact_majorant_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((source (var 1) (var 2) (var 3) (var 4) ⋏ domain (var 6) (var 7) (var 4) (var 5)) ⟶
        bounded (ap2 powerF (var 0) (powerData (var 1) (var 3) (var 6) (var 7)))
          (majorant (var 2) (var 4) (var 5)) one) :=
  closeUniv 8 (.impI (original_power_observation _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactPowerMajorant
