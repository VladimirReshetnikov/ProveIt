import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactExhaustion
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingCell
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianApproximateInverseDistance

/-!
# Scaled Euler exhaustion with independent Gamma observations

The literal inverse scale observation times an ordinary image quadrature
converges to the product of the original inverse scale name and the
original Gamma name at the rescaled parameter. Tail and sampling budgets
give separate numerical clocks. The observation of the target product
can be taken at any independently requested precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionScaled

open_ipra
open GaussianEulerPowerScalingKernel (scaleExpF scaleExpData)
open GaussianEulerPowerScalingCell (scaleSample scaleBound)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerPositivePowerChartImageCompactModulus (nameF data)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B A e f d h L Q k a C E G T : PTm n) : Fm PTm n :=
  GaussianEulerPowerScalingParameter.source z R B A e f L Q ⋏
    (GaussianPositiveRationalLogarithm.source d h ⋏
      (GaussianEulerPositivePowerChartImageCompactModulus.source (scaled z f) (L*R) (B*e) a C E G T ⋏
        (le (a*etaDen k (Q*A) (L*R)) E ⋏ le (top k (Q*A) (L*R)*E) (a+C))))

def referenceF : PR 2 := multiplyF scaleExpF gammaF
def referenceData (z R B A e f d h L Q : PTm n) : PTm n :=
  multiplyData scaleExpF gammaF (scaleExpData z B e f d h) (gammaData (scaled z f) (L*R) (B*e) (Q*A))
def cutoffGain (z R B A e f d h L Q : PTm n) : PTm n :=
  scaleBound z B e f d h*GaussianEulerCompactExhaustion.budget (Q*A) (L*R)
def samplingGain (z R B A e f d h L Q : PTm n) : PTm n :=
  two*scaleBound z B e f d h+
    multiplyModulus scaleExpF gammaF (scaleExpData z B e f d h) (gammaData (scaled z f) (L*R) (B*e) (Q*A))+two
def cutoff (s z R B A e f d h L Q : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (cutoffGain z R B A e f d h L Q) (succ s)
def clock (s z R B A e f d h L Q : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (samplingGain z R B A e f d h L Q) (succ s)

def errorNumerator (K J D P V : PTm n) : PTm n := K*P*V+J*D*V+D*P
def errorDenominator (D P V : PTm n) : PTm n := D*P*V

theorem original_exhaustion_source (z R B A e f d h L Q k a C E G T : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q k a C E G T) :
    Γ ⊢[PRAAx] GaussianEulerCompactExhaustion.source (scaled z f) (L*R) (B*e) (Q*A) k a C E G T :=
  .andI (GaussianEulerPowerScalingParameter.original_rescaled_source z R B A e f L Q hs.andE₁) hs.andE₂.andE₂

theorem reference_regular (z R B A e f d h L Q : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerPowerScalingParameter.source z R B A e f L Q)
    (hd : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source d h) : Γ ⊢[PRAAx]
    pointCN referenceF (referenceData z R B A e f d h L Q) :=
  multiply_fast scaleExpF gammaF _ _
    (GaussianEulerPowerScalingFrozenIntegrand.scale_regular z B e f d h hd)
    (GaussianEulerIntegralGammaIdentification.original_gamma_regular (scaled z f) (L*R) (B*e) (Q*A)
      (GaussianEulerPowerScalingParameter.original_rescaled_source z R B A e f L Q hz))

theorem original_scaled_gamma_observations (p q z R B A e f d h L Q k a C E G T : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q k a C E G T) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (scaleSample p z B e f d h) (ap2 nameF p (data (scaled z f) (L*R) (B*e) a C E G T)))
      (ap2 referenceF q (referenceData z R B A e f d h L Q))
      (errorNumerator (cutoffGain z R B A e f d h L Q) (samplingGain z R B A e f d h L Q)
        (GaussianEulerCompactExhaustion.denominator k) (unit p) (unit q))
      (errorDenominator (GaussianEulerCompactExhaustion.denominator k) (unit p) (unit q)) := by
  let y := scaleExpData z B e f d h
  let x := data (scaled z f) (L*R) (B*e) a C E G T
  let v := gammaData (scaled z f) (L*R) (B*e) (Q*A)
  let w := referenceData z R B A e f d h L Q
  let D := GaussianEulerCompactExhaustion.denominator k
  let K := GaussianEulerCompactExhaustion.budget (Q*A) (L*R)
  let M := scaleBound z B e f d h
  let J := multiplyModulus scaleExpF gammaF y v
  let P := unit p
  let V := unit q
  let H := errorDenominator D P V
  let I₀ := qmul (scaleSample p z B e f d h) (ap2 nameF p x)
  let I₁ := qmul (scaleSample p z B e f d h) (ap2 gammaF p v)
  let I₂ := ap2 referenceF p w
  let I₃ := ap2 referenceF q w
  have hP : Γ ⊢[PRAAx] le one P := unit_positive _
  have hV : Γ ⊢[PRAAx] le one V := unit_positive _
  have hD : Γ ⊢[PRAAx] le one D := unit_positive _
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ (positive_product _ _ hD hP) hV
  have hOuter := original_exhaustion_source z R B A e f d h L Q k a C E G T hs
  have hScale := GaussianEulerPowerScalingFrozenIntegrand.scale_regular z B e f d h hs.andE₂.andE₁
  have hGamma := GaussianEulerIntegralGammaIdentification.original_gamma_regular (scaled z f) (L*R) (B*e) (Q*A) hOuter.andE₁
  have hRef := reference_regular z R B A e f d h L Q hs.andE₁ hs.andE₂.andE₁
  have hBound := GaussianNameBounds.sample_bound scaleExpF y p hScale
  have hRate := GaussianEulerCompactExhaustion.original_gamma_rate (scaled z f) (L*R) (B*e) (Q*A) k a C E G T hOuter
  have observations := rate_at nameF gammaF x v K D p p hRate
  have scaledDistance := GaussianApproximateInverseDistance.multiply_distance (scaleSample p z B e f d h)
    (ap2 nameF p x) (ap2 gammaF p v) M _ _ (GaussianNamedInverseRate.denominator_positive D p p hD) hBound observations
  have left : Γ ⊢[PRAAx] distanceBounded I₀ I₁ ((M*K)*P*V+(two*M)*D*V) H :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive D p p hD) hH
      (le_of_eq_add (d := zero) (by unfold H errorDenominator rateNumerator rateDenominator P V; ipra_ring)) scaledDistance
  have middle : Γ ⊢[PRAAx] distanceBounded I₁ I₂ ((J+one)*D*V) H :=
    distance_radius_mono _ _ _ _ _ _ hP hH
      (le_of_eq_add (d := zero) (by unfold H errorDenominator P; ipra_ring))
      (distance_symmetric _ _ _ _ hP (GaussianNameRingLaws.multiply_sample_error scaleExpF gammaF y v p hScale hGamma))
  have right : Γ ⊢[PRAAx] distanceBounded I₂ I₃ ((P+V)*D) H :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hP hV) hH
      (le_of_eq_add (d := zero) (by unfold H errorDenominator P V; ipra_ring))
      (GaussianNameEquivalence.point_at referenceF w p q hRef)
  have joined := distance_triangle_same _ I₂ _ _ _ H hH (distance_triangle_same _ I₁ _ _ _ H hH left middle) right
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold errorNumerator cutoffGain samplingGain; dsimp only [M,K,J,D,P,V,y,v]; ipra_ring) (.eqRefl _) joined

theorem scheduled_budget (s q K J D p : PTm n)
    (hc : Γ ⊢[PRAAx] le (K*unit (succ s)) D) (hp : Γ ⊢[PRAAx] le (J*unit (succ s)) (unit p)) :
    Γ ⊢[PRAAx] le (errorNumerator K J D (unit p) (unit q)*(unit s*unit q))
      ((unit s+unit q)*errorDenominator D (unit p) (unit q)) := by
  have twice : Γ ⊢[PRAAx] unit (succ s) ≐ unit s*two := pw_succ two s
  have ck := le_congr (congrMul (.eqRefl K) twice) (.eqRefl _) hc
  have cp := le_congr (congrMul (.eqRefl J) twice) (.eqRefl _) hp
  apply RationalValueBounds.positive_cancel (le_succ_self one)
  unfold errorNumerator errorDenominator
  ipra_le (𝔞(unit p)*(𝔞(unit q))^2)*sl ck+(𝔞 D*(𝔞(unit q))^2)*sl cp

theorem original_scheduled_scaled_gamma_observations (s p q z R B A e f d h L Q k a C E G T : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q k a C E G T)
    (hk : Γ ⊢[PRAAx] le (cutoff s z R B A e f d h L Q) k)
    (hp : Γ ⊢[PRAAx] le (clock s z R B A e f d h L Q) p) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (scaleSample p z B e f d h) (ap2 nameF p (data (scaled z f) (L*R) (B*e) a C E G T)))
      (ap2 referenceF q (referenceData z R B A e f d h L Q))
      (unit s+unit q) (unit s*unit q) := by
  let K := cutoffGain z R B A e f d h L Q
  let J := samplingGain z R B A e f d h L Q
  let D := GaussianEulerCompactExhaustion.denominator k
  have c : Γ ⊢[PRAAx] le (K*unit (succ s)) D :=
    le_trans (GaussianFastValueCut.query_budget K (succ s))
      (GaussianExponentialReference.unit_monotone (le_trans hk (le_add_right k (num 6))))
  have j : Γ ⊢[PRAAx] le (J*unit (succ s)) (unit p) :=
    le_trans (GaussianFastValueCut.query_budget J (succ s)) (GaussianExponentialReference.unit_monotone hp)
  have hd : Γ ⊢[PRAAx] le one (errorDenominator D (unit p) (unit q)) :=
    positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) (unit_positive _)
  exact distance_radius_mono _ _ _ _ _ _ hd (positive_product _ _ (unit_positive _) (unit_positive _))
    (scheduled_budget s q K J D p c j)
    (original_scaled_gamma_observations p q z R B A e f d h L Q k a C E G T hs)

theorem actual_scaled_Euler_exhaustion_independent_Gamma_observations_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 19
      (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
        (var 11) (var 12) (var 13) (var 14) (var 15) (var 16) (var 17) (var 18) ⟶
        le (cutoff (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)) (var 13) ⟶
        le (clock (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)) (var 1) ⟶
        distanceBounded
          (qmul (scaleSample (var 1) (var 3) (var 5) (var 7) (var 8) (var 9) (var 10))
            (ap2 nameF (var 1) (data (scaled (var 3) (var 8)) (var 11*var 4) (var 5*var 7)
              (var 14) (var 15) (var 16) (var 17) (var 18))))
          (ap2 referenceF (var 2) (referenceData (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
            (var 10) (var 11) (var 12)))
          (unit (var 0)+unit (var 2)) (unit (var 0)*unit (var 2))) :=
  closeUniv 19 (.impI (.impI (.impI (original_scheduled_scaled_gamma_observations
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionScaled
