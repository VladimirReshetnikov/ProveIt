import IPRADerivations.Analysis.Euler.CompactExhaustion.ParameterBounds.GaussianEulerCompactPowerMajorant
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalRoundedPower

/-!
# Replacing the decay factor of an original compact Euler sample

An exact rational replacement for the decay factor is compared with
the original decay at the actual multiplication clock. The power
factor at that same clock is unchanged. The compact power majorant
amplifies the supplied factor error, and the two independent
observation errors come from the original product-to-integrand law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactProductComparison

open_ipra
open GaussianEulerIntegrandName (powerF powerData decayF decayData productF productData nameF data)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianEulerExponentCompactBounds (source)
open GaussianCompactLogarithmBounds (domain)
open GaussianRationalHorner (qmul qmul_canonical)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (multiplyModulus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def clock (p z B a b : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus powerF decayF (powerData z B a b) (decayData a b)) p

ipra_subst clock [decayData, GaussianGammaFiniteApproximantName.exponentialInputData]

theorem clock_later (p z B a b : PTm n) : Γ ⊢[PRAAx] le p (clock p z B a b) :=
  le_add_right _ _

def replacement (p z B a b w : PTm n) : PTm n :=
  qmul (ap2 powerF (clock p z B a b) (powerData z B a b)) w

ipra_subst replacement

theorem original_product (p z B a b : PTm n) :
    Γ ⊢[PRAAx] ap2 productF p (productData z B a b) ≐
      replacement p z B a b (ap2 decayF (clock p z B a b) (decayData a b)) :=
  (GaussianNameArithmetic.multiply_at powerF decayF (powerData z B a b) (decayData a b) p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))

theorem replacement_error (p q z R B E T a b w U V : PTm n) (hz : Γ ⊢[PRAAx] source z R B E)
    (ht : Γ ⊢[PRAAx] domain a b E T) (hV : Γ ⊢[PRAAx] le one V)
    (hw : Γ ⊢[PRAAx] distanceBounded w (ap2 decayF (clock p z B a b) (decayData a b)) U V) :
    Γ ⊢[PRAAx] distanceBounded (replacement p z B a b w) (ap2 nameF q (data z B a b))
      ((majorant R E T*U)*(unit p*unit q)+(unit p+unit q)*V) (V*(unit p*unit q)) := by
  let k := clock p z B a b
  let x := ap2 powerF k (powerData z B a b)
  let y := ap2 decayF k (decayData a b)
  let K := majorant R E T
  have pbound := GaussianEulerCompactPowerMajorant.original_power_observation k z R B E T a b hz ht
  have first : Γ ⊢[PRAAx] distanceBounded (replacement p z B a b w) (ap2 productF p (productData z B a b)) (K*U) V := by
    have productBound : Γ ⊢[PRAAx] distanceBounded (qmul x w) (qmul x y) (K*U) V :=
      GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference x w y).eqSymm
        (.eqRefl _) (by ipra_ring)
        (GaussianRationalReciprocal.bounded_product x _ K one U V (le_refl _) hV pbound hw)
    exact distance_congr (.eqRefl _) (original_product p z B a b).eqSymm (.eqRefl _) (.eqRefl _) productBound
  have equivalent := GaussianEulerIntegrandName.original_power_times_decay z B a b (.andI hz.andE₁ ht.andE₁)
  have second := GaussianNameEquivalence.cross_at productF nameF (productData z B a b) (data z B a b) p q equivalent
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hV
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive q)) first second

theorem original_Euler_compact_replaced_factor_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      ((source (var 2) (var 3) (var 4) (var 5) ⋏ domain (var 7) (var 8) (var 5) (var 6)) ⟶
       (le one (var 11) ⋏ distanceBounded (var 9)
         (ap2 decayF (clock (var 0) (var 2) (var 4) (var 7) (var 8)) (decayData (var 7) (var 8)))
         (var 10) (var 11)) ⟶
       distanceBounded (replacement (var 0) (var 2) (var 4) (var 7) (var 8) (var 9))
         (ap2 nameF (var 1) (data (var 2) (var 4) (var 7) (var 8)))
         ((majorant (var 3) (var 5) (var 6)*var 10)*(unit (var 0)*unit (var 1))+
           (unit (var 0)+unit (var 1))*var 11) (var 11*(unit (var 0)*unit (var 1)))) :=
  closeUniv 12 (.impI (.impI
    (replacement_error _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactProductComparison
