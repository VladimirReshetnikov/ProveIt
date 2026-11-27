import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.Pointwise.GaussianEulerLogarithmicParameterRemainder

/-!
# Source-only pointwise Taylor bound for the original Euler logarithmic row

The actual native parameter sum represents z/B+h/D exactly. The original
compact disk and the proved unit increment bound derive its disk R+1.
Consequently the original logarithmic evaluators at orders j and j+1
satisfy a quadratic parameter error from the single original compact
source and the actual small increment. No shifted output or Taylor-error
certificate is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicParameterTaylor

open_ipra
open GaussianRationalPowerDifference (bounded_sum_one)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianEulerLogarithmicParameterIncrement (source curvature)
open GaussianEulerLogarithmicParameterRemainder (actualLinear numerator denominator)
open GaussianRationalHorner (qadd ofGaussian represents positive_product)
open GaussianRationalMetric (bounded distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem encoded_sum (z B h D : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    ofGaussian (shifted z B h D) (B*D) ≐ qadd (ofGaussian z B) (ofGaussian h D) := by
  have bd := positive_product _ _ hB hD
  have first := GaussianRationalHorner.represents_rescale _ _ _ D (GaussianRationalHorner.ofGaussian_represents z B hB)
  have second := GaussianRationalSyntheticDivision.rescale_to _ _ _ B (B*D)
    (GaussianRationalHorner.ofGaussian_represents h D hD) (mul_comm _ _)
  have right := GaussianRationalHorner.qadd_represents _ _ _ _ _ bd first second
  exact GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ bd)
    (GaussianRationalHorner.qadd_canonical _ _) bd (GaussianRationalHorner.ofGaussian_represents _ _ bd) right

theorem shifted_disk (z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (shifted z B h D) ((R+one)*(B*D)) := by
  have hB := hs.andE₁.andE₁.andE₁
  have hD := hs.andE₂.andE₁
  have bd := positive_product _ _ hB hD
  have left := GaussianGammaEulerHead.fraction_disk z R B hB hs.andE₁.andE₁.andE₂.andE₂
  have right := GaussianEulerParameterIncrementObservation.parameter_unit_bound z R B E T a b h D X Y hs
  have actual : Γ ⊢[PRAAx] bounded (ofGaussian (shifted z B h D) (B*D)) (R+one) one :=
    GaussianRationalReciprocal.bound_congr (encoded_sum z B h D hB hD).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_sum_one left right)
  have clear := GaussianRationalMetric.bounded_to_cleared _ _ (B*D) (R+one) one bd (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents _ _ bd) actual
  exact le_congr (by ipra_ring) (by ipra_ring) clear

theorem original_input (z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicParameterRemainder.input z R (R+one) B E T a b h D X Y :=
  .andI hs (.andI
    (.andI (positive_product _ _ hs.andE₁.andE₁.andE₁ hs.andE₂.andE₁)
      (.andI hs.andE₁.andE₁.andE₂.andE₁ (shifted_disk z R B E T a b h D X Y hs))) hs.andE₁.andE₂)

/-- Actual first-order Taylor error at every runtime logarithmic order,
with radius R+1 derived internally and all three observations independent. -/
theorem original_parameter_taylor (p q r j z R B E T a b h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B E T a b h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerLogarithmicCompactName.sample p j (R+one) E T (shifted z B h D) (B*D) a b)
      (actualLinear q r j z R B E T a b h D) (numerator p q r j R E T X Y) (denominator p q r Y) :=
  GaussianEulerLogarithmicParameterRemainder.original_parameter_remainder p q r j z R (R+one) B E T a b h D X Y
    (original_input z R B E T a b h D X Y hs)

theorem original_source_only_all_orders_parameter_Taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
    (source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) ⟶
      distanceBounded
        (GaussianEulerLogarithmicCompactName.sample (var 0) (var 3) (var 5+one) (var 7) (var 8)
          (shifted (var 4) (var 6) (var 11) (var 12)) (var 6*var 12) (var 9) (var 10))
        (actualLinear (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 5) (var 7) (var 8) (var 13) (var 14))
        (denominator (var 0) (var 1) (var 2) (var 14))) :=
  closeUniv 15 (.impI (original_parameter_taylor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicParameterTaylor
