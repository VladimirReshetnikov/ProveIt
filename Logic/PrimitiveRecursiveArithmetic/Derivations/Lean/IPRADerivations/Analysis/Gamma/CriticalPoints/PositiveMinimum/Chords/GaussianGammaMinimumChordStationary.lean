import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.Chords.GaussianGammaMinimumChordReadback
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# The strong Gamma chord at an approximately stationary base

A center-to-base logarithmic rate with denominator W*N contributes a
leading K/N after applying the chord of weight W. The finite rational
gap removes the auxiliary query. The remaining errors are precisely
the two independent observations of the original log-Gamma name.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumChordStationary

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaMinimumChord (centerData margin)
open GaussianGammaMinimumChordReadback (budget difference_at log_sample_canonical)
open GaussianNameEquivalence (point_at)
open GaussianNameRingLaws (sum_right_error)
open GaussianNamedInverseRate (denominator_positive diagonal_rate independentRate rateNumerator rateDenominator)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianNamedRealOrderTransport (precision upperSlack remove_upper_slack)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd qzero ofGaussian_canonical positive_product)
open GaussianRationalLinearProduct (add_sub_right)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalNaturalScale (natScale naturalPoint natScale_as_product)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right)
open GaussianReconstructionRoots (distance_zero_iff)
open GaussianStirlingGammaLogarithm (logGammaF logGammaData log_gamma_regular)
open GaussianStirlingTailComparison (point_add_upper_same point_order_refl)
open RationalValueBounds (upper upper_congr upper_mono upper_of_order upper_of_radius upper_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => logGammaF
local notation "lg" => logGammaData

def observationCost (a c b W : PTm n) : PTm n := two*W+budget a c b W

ipra_subst observationCost [two]

private theorem center_displacement (t a c b W K N : PTm n) (hW : Γ ⊢[PRAAx] le two W)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b W) (lg a b) K (W*N)) :
    Γ ⊢[PRAAx] distanceBounded
      (natScale W (qsub (ap2 G t (centerData a c b W)) (ap2 G t (lg a b)))) qzero
      (K*unit t+two*W*N) (N*unit t) := by
  let U := unit t
  let X := ap2 G t (lg a b)
  let Z := ap2 G t (centerData a c b W)
  let d := qsub Z X
  let E := (W*N)*U
  have hU := unit_positive (Γ := Γ) t
  have hWN := positive_product _ _ (le_trans RationalAlgebra.two_positive hW) hN
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hWN hU
  have hNU := positive_product _ _ hN hU
  have small : Γ ⊢[PRAAx] bounded d (K*U+two*(W*N)) E :=
    diagonal_rate G G (centerData a c b W) (lg a b) K (W*N) t hWN h
  have product : Γ ⊢[PRAAx] bounded (natScale W d) (W*(K*U+two*(W*N))) E :=
    bound_congr (natScale_as_product W d).eqSymm (.eqRefl _) (one_mul E)
      (bounded_product _ _ _ _ _ _ (le_refl one) hE (GaussianNamedNaturalScale.natural_point_bound W) small)
  have scaled : Γ ⊢[PRAAx] bounded (natScale W d) (K*U+two*W*N) (N*U) :=
    bounded_radius_mono _ _ _ _ _ hE hNU (by unfold E; exact le_of_eq_add (d := zero) (by ipra_ring)) product
  exact (distance_zero_iff _ _ _ hNU).iffMpr scaled

/-- Before removing the auxiliary query, the only additional slack is
the fixed chord readback cost and twice the weight at that query. -/
theorem diagonal_at (t a c b M W K N : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hc : Γ ⊢[PRAAx] le one c)
    (hb : Γ ⊢[PRAAx] le one b) (haM : Γ ⊢[PRAAx] le a (M*b)) (hcM : Γ ⊢[PRAAx] le c (M*b))
    (hW : Γ ⊢[PRAAx] le two W) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b W) (lg a b) K (W*N)) :
    Γ ⊢[PRAAx] upper (fstT (qadd (margin a c b M) (ap2 G t (lg a b)))) (fstT (ap2 G t (lg c b)))
      (K*unit t+observationCost a c b W*N) (N*unit t) := by
  let U := unit t
  let X := ap2 G t (lg a b)
  let Y := ap2 G t (lg c b)
  let Z := ap2 G t (centerData a c b W)
  let g := margin a c b M
  let d := natScale W (qsub Z X)
  let A := K*U+observationCost a c b W*N
  let D := N*U
  have hU := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hN hU
  have hB := le_trans ha haM
  have h4 : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have hg : Γ ⊢[PRAAx] GaussianRationalHorner.canonical g :=
    ofGaussian_canonical _ _ (positive_product _ _ (positive_product _ _ h4 hB) hB)
  have close : Γ ⊢[PRAAx] distanceBounded d qzero (K*U+two*W*N) D :=
    center_displacement t a c b W K N hW hN h
  have move : Γ ⊢[PRAAx] distanceBounded g (qadd g d) (K*U+two*W*N) D :=
    distance_congr (qadd_zero_right g hg) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (sum_right_error g qzero d _ _ hD (distance_symmetric _ _ _ _ hD close))
  have before := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hD move)
  have chord := difference_at t a c b M W ha hc hb haM hcM hW
  have joined : Γ ⊢[PRAAx] upper (fstT g) (fstT (qsub Y X)) A D :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hD hU) (upper_triangle _ _ _ _ _ _ _ before chord)
      (le_of_eq_add (d := zero) (by unfold A D observationCost; ipra_ring))
  have id : Γ ⊢[PRAAx] upper (fstT X) (fstT X) zero D :=
    upper_of_order _ _ _ _ (point_order_refl _)
  have added := point_add_upper_same _ _ _ _ _ _ _ hD joined id
  have read : Γ ⊢[PRAAx] qadd (qsub Y X) X ≐ Y :=
    (qadd_commutative (qsub Y X) X).eqTrans (add_sub_right X Y (log_sample_canonical t c b))
  exact upper_congr (.eqRefl _) (congrFst read) (LeanProofs.IPRA.add_zero A) (.eqRefl _) added

private theorem observation_slack (p q t a c b M W K N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b)
    (haM : Γ ⊢[PRAAx] le a (M*b)) (hcM : Γ ⊢[PRAAx] le c (M*b))
    (hW : Γ ⊢[PRAAx] le two W) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b W) (lg a b) K (W*N)) :
    Γ ⊢[PRAAx] upperSlack (fstT (qadd (margin a c b M) (ap2 G p (lg a b)))) (fstT (ap2 G q (lg c b)))
      (rateNumerator K N p q) (rateDenominator N p q) (observationCost a c b W+two) t := by
  let P := unit p
  let Q := unit q
  let U := unit t
  let g := margin a c b M
  let x := lg a b
  let y := lg c b
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hU := unit_positive (Γ := Γ) t
  have hPU := positive_product _ _ hP hU
  have hNU := positive_product _ _ hN hU
  have hUQ := positive_product _ _ hU hQ
  have left : Γ ⊢[PRAAx] distanceBounded (qadd g (ap2 G p x)) (qadd g (ap2 G t x)) (P+U) (P*U) :=
    sum_right_error g _ _ _ _ hPU (point_at G x p t (log_gamma_regular a b (.andI ha hb)))
  have right := point_at G y t q (log_gamma_regular c b (.andI hc hb))
  have before := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hPU left)
  have after := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hUQ right)
  have inside := diagonal_at t a c b M W K N ha hc hb haM hcM hW hN h
  have joined := upper_triangle _ _ _ _ _ _ _ (upper_triangle _ _ _ _ _ _ _ before inside) after
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hPU hNU) hUQ) joined
  exact le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)

/-- The unscaled log-Gamma comparison retains only K/N and the two
independent original observation allowances. -/
theorem stationary_at (p q a c b M W K N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b)
    (haM : Γ ⊢[PRAAx] le a (M*b)) (hcM : Γ ⊢[PRAAx] le c (M*b))
    (hW : Γ ⊢[PRAAx] le two W) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b W) (lg a b) K (W*N)) :
    Γ ⊢[PRAAx] upper (fstT (qadd (margin a c b M) (ap2 G p (lg a b)))) (fstT (ap2 G q (lg c b)))
      (rateNumerator K N p q) (rateDenominator N p q) :=
  remove_upper_slack _ _ _ _ (observationCost a c b W+two)
    (observation_slack p q (precision (fstT (qadd (margin a c b M) (ap2 G p (lg a b)))) (fstT (ap2 G q (lg c b)))
      (rateDenominator N p q) (observationCost a c b W+two)) a c b M W K N ha hc hb haM hcM hW hN h)

theorem stationary_diagonal (p a c b M W K N : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hc : Γ ⊢[PRAAx] le one c) (hb : Γ ⊢[PRAAx] le one b)
    (haM : Γ ⊢[PRAAx] le a (M*b)) (hcM : Γ ⊢[PRAAx] le c (M*b))
    (hW : Γ ⊢[PRAAx] le two W) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] independentRate G G (centerData a c b W) (lg a b) K (W*N)) :
    Γ ⊢[PRAAx] upper (fstT (qadd (margin a c b M) (ap2 G p (lg a b)))) (fstT (ap2 G p (lg c b)))
      (K*unit p+two*N) (N*unit p) :=
  upper_mono _ _ _ _ _ _ (denominator_positive N p p hN)
    (stationary_at p p a c b M W K N ha hc hb haM hcM hW hN h)
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumChordStationary
