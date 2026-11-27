import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.FiniteRows.GaussianBinetSecondDecayPointwise
import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.ExponentialScaling.GaussianBinetBoseExponential
import IPRADerivations.Analysis.Stirling.Binet.Kernel.HyperbolicForm.ImaginaryRatios.GaussianBinetKernelImaginaryRatioCofinal

/-!
# Freezing the signed pi exponent at a compact time budget

The original second Binet exponent uses the signed pi-scaled name.
On a fixed positive time interval, the same coefficient can use a
uniform normalization clock and a uniform exponential radius. A
frozen pi sample then gives the literal rational decay already used
by the finite tail estimates, at an error independent of the mesh.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayPiBridge

open_ipra
open GaussianBinetSecondDecayPointwise (frozenPiNumerator angle row)
open GaussianBinetBoseExponential (expF expData scaleF scaleData scaleBudget expRadius)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianNamedInverseRate (independentRate)
open GaussianNameEquivalence (cross_symm cross_trans cross_refl)
open GaussianNameBounds (U)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded qnegative)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneLogarithm (source)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianStirlingConstant (piNumerator piDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "Pi" => GaussianGammaHalfPiName.nameF
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data

def cap (m T : PTm n) : PTm n := two*m*T
def radius (m T : PTm n) : PTm n := cap m T*U Pi zero
def budget (m T : PTm n) : PTm n :=
  GaussianRadiusExponentialLipschitzRate.factor (radius m T)*(cap m T*(zero+two))

ipra_subst budget [radius, cap, one, two]

theorem budget_monotone (m M T : PTm n) (hm : Γ ⊢[PRAAx] le m M) :
    Γ ⊢[PRAAx] le (budget m T) (budget M T) := by
  have hC : Γ ⊢[PRAAx] le (cap m T) (cap M T) :=
    le_congr (by unfold cap; ipra_ring) (by unfold cap; ipra_ring) (mul_le_mul_right (two*T) hm)
  have hR : Γ ⊢[PRAAx] le (radius m T) (radius M T) := mul_le_mul_right (U Pi zero) hC
  have hF : Γ ⊢[PRAAx] le (GaussianRadiusExponentialLipschitzRate.factor (radius m T))
      (GaussianRadiusExponentialLipschitzRate.factor (radius M T)) :=
    GaussianFactorBudget.power_monotone_length (num 3) _ _ (by ipra_le 2) hR
  exact le_mul_mono hF (mul_le_mul_right (zero+two) hC)

theorem frozen_argument (k m a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (GaussianPiRationalScale.point true (two*(m*a)) b) (GaussianBinetKernelPi.sample k) ≐
      decayPoint (two*(a*frozenPiNumerator m k)) (b*piDenominator k) := by
  let A := two*(m*a)
  let P := piNumerator k
  let Q := piDenominator k
  let c := GaussianPiRationalScale.point false A b
  let z := GaussianBinetKernelPi.sample k
  have hQ := GaussianBinetKernelPi.denominator_positive (Γ := Γ) k
  have e := (GaussianBinetKernelPi.sample_fraction (Γ := Γ) k).eqTrans
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point P Q hQ)
  have hp : Γ ⊢[PRAAx] qmul c z ≐ GaussianPositiveRationalLogarithm.fraction (two*(a*frozenPiNumerator m k)) (b*Q) :=
    (qmul_congr (.eqRefl c) e).eqTrans
      ((GaussianDominantPairAlgebra.radius_multiply A b P Q hb hQ).eqTrans
        (((GaussianEulerDecayFactorBounds.fraction_is_radius_point (A*P) (b*Q) (positive_product _ _ hb hQ)).eqSymm).eqTrans
          (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by dsimp only [A,P,frozenPiNumerator]; ipra_ring) (.eqRefl _))))
  exact (qmul_congr (GaussianPiRationalScale.point_negate false A b hb).eqSymm (.eqRefl z)).eqTrans
    ((GaussianInverseBinomialRows.negative_product c z).eqSymm.eqTrans (GaussianInverseBinomialRows.negative_congr hp))

theorem uniform_rate (k m a b T : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] independentRate expF decayF (expData true (m*a) b)
      (decayData (two*(a*frozenPiNumerator m k)) (b*piDenominator k)) (budget m T) (unit k) := by
  let A := m*a
  let C := cap m T
  let S := radius m T
  let c := GaussianPiRationalScale.point true (two*A) b
  let x := GaussianPiRationalScale.data true (two*A) b C zero
  let z := GaussianBinetKernelPi.sample k
  let y := decayPoint (two*(a*frozenPiNumerator m k)) (b*piDenominator k)
  let G := GaussianBoundedConstantProductName.nameF constantF
  let g := GaussianBoundedConstantProductName.data C c z
  have hk := unit_positive (Γ := Γ) k
  have hC : Γ ⊢[PRAAx] le (two*A) (C*b) :=
    le_congr (by dsimp only [A]; ipra_ring) (by dsimp only [C,cap]; ipra_ring) (mul_le_mul_right (two*m) ht)
  have hOld : Γ ⊢[PRAAx] le (two*A) (scaleBudget A*b) :=
    le_trans (le_add_right _ one)
      (le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (scaleBudget A) hb))
  have hc : Γ ⊢[PRAAx] bounded c C one :=
    GaussianPiRationalScale.point_bound true (two*A) b C one hb (le_refl one)
      (le_congr (one_mul _).eqSymm (.eqRefl _) hC)
  have piRegular := GaussianGammaHalfPiName.name_regular (Γ := Γ) zero
  have freeze : Γ ⊢[PRAAx] distanceBounded (ap2 Pi k zero) (ap2 constantF k z) zero (unit k) :=
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (constant_at k z).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianRationalPowerDifference.distance_refl_zero z (unit k) hk)
  have piRate := GaussianBinetKernelImaginaryRatioCofinal.anchored_rate Pi constantF zero z k zero
    piRegular (constant_regular z) freeze
  have scaleRate := GaussianBoundedConstantProductRate.original_rate Pi constantF C c zero z _ _ hk hc piRate
  have product := frozen_argument k m a b hb
  have constBinding := cross_trans _ _ _ _ _ _
    (GaussianBoundedConstantProductName.ordinary_product_identity constantF C c z (.andI (constant_regular z) hc))
    (cross_trans _ _ _ _ _ _ (constant_product_cross c z) (constant_data_cross (qmul c z) y product))
  have scaled : Γ ⊢[PRAAx] independentRate scaleF constantF x y (C*(zero+two)) (unit k) :=
    GaussianNamedRateTransport.transport scaleF G scaleF constantF x g x y _ _ hk scaleRate
      (cross_refl _ _ (GaussianPiRationalScale.regular true (two*A) b C zero hb hC))
      (cross_symm _ _ _ _ constBinding)
  have xy : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input scaleF S x :=
    GaussianPiRationalScale.exponential_input true (two*A) b C zero hb hC
  have raw := bounded_product c z C one (U Pi zero) one (le_refl one) (le_refl one) hc
    (GaussianNameBounds.sample_bound Pi zero k piRegular)
  have cy : Γ ⊢[PRAAx] bounded y S one := bound_congr product (.eqRefl _) (one_mul one) raw
  have iy := GaussianSignedNameExponentialOrder.constant_input y S cy
  have newRate := GaussianRadiusExponentialLipschitzRate.independent_rate scaleF constantF S x y (C*(zero+two))
    (unit k) (.andI hk (.andI xy (.andI iy scaled)))
  have sender := cross_trans _ _ _ _ _ _
    (GaussianPiRationalScale.ordinary true (two*A) b (scaleBudget A) zero hb hOld)
    (cross_symm _ _ _ _ (GaussianPiRationalScale.ordinary true (two*A) b C zero hb hC))
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper scaleF scaleF (expRadius A) S
    (scaleData true A b) x (GaussianBinetBoseExponential.exp_input true A b hb) xy sender
  have iyOld := GaussianGammaFiniteApproximantName.exponential_input (Γ := Γ) constantF y (constant_regular y)
  have right := GaussianExponentialRadiusIndependence.same_input_cross constantF (U constantF y) S y iyOld iy
  exact GaussianNamedRateTransport.transport expF (Exp constantF) expF decayF (ed S x) (ed S y)
    (expData true A b) (decayData (two*(a*frozenPiNumerator m k)) (b*piDenominator k))
    (budget m T) (unit k) hk newRate left right

theorem diagonal_error (p k m a b T : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b))
    (hk : Γ ⊢[PRAAx] le (budget m T*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 expF p (expData true (m*a) b))
      (ap2 decayF p (decayData (two*(a*frozenPiNumerator m k)) (b*piDenominator k))) (num 3) (unit p) := by
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) k
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hv hu) hu
    (by ipra_le 𝔞(unit p)*sl hk)
    (GaussianNamedInverseRate.diagonal_rate _ _ _ _ _ _ p hv (uniform_rate k m a b T hb ht))

theorem angular_row_error (p k m a b T K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b))
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hk : Γ ⊢[PRAAx] le (budget m T*unit p) (unit k)) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (angle p X Y D sign a b) (ap2 expF p (expData true (m*a) b)))
      (row p X Y D sign a b (frozenPiNumerator m k) (piDenominator k)) (num 3*K*T) (unit p) := by
  let v := angle p X Y D sign a b
  have h := positive_product _ _ hb hz.andE₁.andE₁
  have hv : Γ ⊢[PRAAx] bounded v (K*T) one :=
    bounded_radius_mono _ _ _ _ _ h (le_refl one)
      (by ipra_le 𝔞(D)*sl ht+𝔞(T)*𝔞(b)*sl hK)
      (GaussianBinetArctangentQuadratureBound.name_bound p X Y D sign a b hz hb)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance v _ _ (K*T) (num 3) (unit p)
      (unit_positive p) hv (diagonal_error p k m a b T hb ht hk))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayPiBridge
