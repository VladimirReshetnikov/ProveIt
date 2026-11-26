import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianNamedSincRatio
import IPRADerivations.Analysis.FiniteOperations.GaussianInverseSquareProductComparison
import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductT4Budget

/-!
# A finite product row from independently clocked sinc observations

The row compares the ratio-corrected factor with the literal factor
(1-z^2/k^2). Both the argument radii and the denominator of the error
use the explicit multiple of (T4).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSincRatioProductRow

open_ipra
open GaussianNamedSincRatio (ratio ratio_error)
open GaussianNamedSincQuadraticBounds (observationBound quadratic_bound)
open GaussianNamedSinc (nameF data)
open GaussianSineProductT4Budget (multiple squareDenominator multiple_positive denominator_positive argument_disk root_disk)
open GaussianGammaEulerReflectionHead (squareFactor)
open GaussianInverseSquareProductComparison (rowErrorNumerator rowErrorDenominator)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qmul qmul_canonical positive_product)
open GaussianRationalMetric (bounded bounded_iff distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalReciprocal (qone bound_congr bounded_product)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianNamedDifference (difference_distance)
open GaussianReciprocalHorner (qmul_one_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def baseSquare (i z B : PTm n) : PTm n :=
  qmul (ofGaussian z (B*succ i)) (ofGaussian z (B*succ i))

def value (f g : PR 2) (N x S y p q z B i : PTm n) : PTm n :=
  qsub qone (qmul (baseSquare i z B) (ratio f g N x S y p q))

ipra_subst baseSquare
ipra_subst value

theorem base_square_bound (i z R B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (baseSquare i z B) (R*R) (succ i*succ i) := by
  let k := succ i
  let D := B*k
  let a := ofGaussian z D
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hD := positive_product B k hB hk
  have ha : Γ ⊢[PRAAx] bounded a R k := (bounded_iff a z D R k hD hk (ofGaussian_represents _ _ hD)).iffMpr
    (le_congr (by ipra_ring) (by dsimp only [D]; ipra_ring) (mul_le_mul_right (k*k) hz))
  exact bounded_product _ _ _ _ _ _ hk hk ha ha

theorem prefactor_small (f : PR 2) (N x p R K : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] observationBound f x (num 4*R) (multiple R K)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data f N x)) qone (num 8*(R*R)) (squareDenominator R K) := by
  let M := multiple R K
  let D := squareDenominator R K
  have hM := multiple_positive (Γ := Γ) R K
  have hD := denominator_positive (Γ := Γ) R K
  have h2D := positive_product _ _ (le_succ_self one) hD
  have q := quadratic_bound f N x (num 4*R) M p hM (argument_disk R K hR hK) h
  exact distance_radius_mono _ _ _ _ _ _ h2D hD
    (le_of_eq_add (d := zero) (by ipra_ring)) q

theorem row_error (f g : PR 2) (N x S y p q z R B K i : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K)
    (hi : Γ ⊢[PRAAx] lt i K) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hu : Γ ⊢[PRAAx] observationBound f x (num 4*R) (multiple R K))
    (hv : Γ ⊢[PRAAx] observationBound g y (num 4*succ i) (multiple R K)) :
    Γ ⊢[PRAAx] distanceBounded (value f g N x S y p q z B i) (squareFactor i z B)
      (rowErrorNumerator (num 96*(R*R)) (R*R) i) (rowErrorDenominator (squareDenominator R K) i) := by
  let k := succ i
  let M := multiple R K
  let D := squareDenominator R K
  let T := num 96*(R*R+k*k)
  let a := baseSquare i z B
  let b := ratio f g N x S y p q
  have hM := multiple_positive (Γ := Γ) R K
  have hD := denominator_positive (Γ := Γ) R K
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hkk := positive_product k k hk hk
  have hb : Γ ⊢[PRAAx] distanceBounded b qone T D :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hD hD) hD
      (le_of_eq_add (d := zero) (by dsimp only [T,D,k,M,squareDenominator]; ipra_ring))
      (ratio_error f g N x S y (num 4*R) M (num 4*k) M p q hM (argument_disk R K hR hK)
        hM (root_disk R K k hR hK hi) hu hv)
  have prod := bounded_product _ _ _ _ _ _ hkk hD (base_square_bound i z R B hB hz) hb
  have step : Γ ⊢[PRAAx] distanceBounded (qmul a b) a ((R*R)*T) ((k*k)*D) :=
    distance_congr (.eqRefl _) (qmul_one_right a (qmul_canonical _ _)) (.eqRefl _) (.eqRefl _)
      (bound_congr (GaussianRationalRoundedPower.multiplication_difference a b qone).eqSymm
        (.eqRefl _) (.eqRefl _) prod)
  have hden := positive_product _ _ hkk hD
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold rowErrorNumerator; dsimp only [T,k]; ipra_ring)
    (by unfold rowErrorDenominator; dsimp only [k]; ipra_ring)
    (difference_distance qone qone _ _ zero _ _ hden (distance_refl_zero qone _ hden) step)

end LeanProofs.IPRA.Analysis.GaussianSincRatioProductRow
