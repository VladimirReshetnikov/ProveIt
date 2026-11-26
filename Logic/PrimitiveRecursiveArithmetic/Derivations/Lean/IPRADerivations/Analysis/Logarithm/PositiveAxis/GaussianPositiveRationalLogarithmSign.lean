import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport
import IPRADerivations.AnalyticNumberTheory.HarmonicChebyshev

/-!
# The original positive-time logarithm has the correct sign at one

The exact same finite harmonic intervals have the correct sign. Their
proved original-sample error and original pointCN give one finite
upper-gap comparison. Removing that auxiliary error leaves exactly the
requested original logarithm observation error, on each side of t=1.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmSign

open_ipra
open GaussianPositiveRationalLogarithm (source sample logF data name_regular)
open RationalHarmonicInterval (interval horizon numerator common_value)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open GaussianRationalSyntheticBounds (natCode)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_of_radius upper_triangle)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem interval_nonpositive (a b Q : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    rationalLE (interval a b Q) (natCode zero) := by
  let L := horizon a b Q
  let F := Products.fact L
  have order := S_mono (Γ := Γ) F (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right Q h))
  apply RationalArithmetic.order_of_representations _ _ (numerator a b Q L) (ZT.ofNat zero) F one
    (common_value a b Q L) (GaussianRationalSyntheticBounds.natCode_represents zero)
    (GammaEulerMesh.factorial_positive L) (le_refl one)
  apply zle_of_toZ (monus (S (Q*b) F) (S (Q*a) F))
  have e := natEq (eq_add_of_le order)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  simp only [F] at e
  ipra_simps
  linear_combination -e

theorem interval_nonnegative (a b Q : PTm n) (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    rationalLE (natCode zero) (interval a b Q) := by
  let L := horizon a b Q
  let F := Products.fact L
  have order := S_mono (Γ := Γ) F (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right Q h))
  apply RationalArithmetic.order_of_representations _ _ (ZT.ofNat zero) (numerator a b Q L) one F
    (GaussianRationalSyntheticBounds.natCode_represents zero) (common_value a b Q L)
    (le_refl one) (GammaEulerMesh.factorial_positive L)
  apply zle_of_toZ (monus (S (Q*a) F) (S (Q*b) F))
  have e := natEq (eq_add_of_le order)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  simp only [F] at e
  ipra_simps
  linear_combination -e

theorem embedded_interval_nonpositive (a b Q : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    rationalLE (fstT (RationalGaussianEmbedding.embed (interval a b Q))) (natCode zero) :=
  RationalArgmin.rationalLE_congr (fst_pair _ _).eqSymm (.eqRefl _)
    (RationalArgmin.transitive (RationalArgmin.eq_le (RationalArithmetic.recode_equal _)) (interval_nonpositive a b Q h))

theorem embedded_interval_nonnegative (a b Q : PTm n) (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    rationalLE (natCode zero) (fstT (RationalGaussianEmbedding.embed (interval a b Q))) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (fst_pair _ _).eqSymm
    (RationalArgmin.transitive (interval_nonnegative a b Q h) (RationalArgmin.eq_le (RationalArithmetic.recode_equal _).eqSymm))

theorem upper_budget (a b p t : PTm n) (hs : Γ ⊢[PRAAx] source a b) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack (fstT (sample p a b)) (natCode zero) one (unit p) (num 9) t := by
  have near := GaussianNameEquivalence.point_at logF (data a b) p t (name_regular a b hs)
  have first := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive t)) near)
  have err := GaussianPositiveRationalLogarithmProperness.sample_interval_error t a b hs
  have second := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ (unit_positive t) err)
  have joined := RationalValueBounds.upper_order_right _ _ _ _ _
    (upper_triangle _ _ _ _ _ _ _ first second) (embedded_interval_nonpositive a b (GammaEulerConstantName.mesh t) h)
  apply RationalValueBounds.upper_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _
      (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive t)) (unit_positive t)) joined
  exact le_of_eq_add (d := zero) (by ipra_ring)

theorem lower_budget (a b p t : PTm n) (hs : Γ ⊢[PRAAx] source a b) (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack (natCode zero) (fstT (sample p a b)) one (unit p) (num 9) t := by
  have err := GaussianPositiveRationalLogarithmProperness.sample_interval_error t a b hs
  have first := RationalValueBounds.upper_order_left _ _ _ _ _
    (embedded_interval_nonnegative a b (GammaEulerConstantName.mesh t) h)
    (upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _
      (scalar_coordinate_distance _ _ _ _ (unit_positive t) err)))
  have near := GaussianNameEquivalence.point_at logF (data a b) t p (name_regular a b hs)
  have second := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive t) (unit_positive p)) near)
  have joined := upper_triangle _ _ _ _ _ _ _ first second
  apply RationalValueBounds.upper_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive t)
      (GaussianRationalHorner.positive_product _ _ (unit_positive t) (unit_positive p))) joined
  exact le_of_eq_add (d := zero) (by ipra_ring)

theorem original_logarithm_nonpositive (a b p : PTm n) (hs : Γ ⊢[PRAAx] source a b) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    upper (fstT (sample p a b)) (natCode zero) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ (num 9)
    (upper_budget a b p (GaussianNamedRealOrderTransport.precision (fstT (sample p a b)) (natCode zero) (unit p) (num 9)) hs h)

theorem original_logarithm_nonnegative (a b p : PTm n) (hs : Γ ⊢[PRAAx] source a b) (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    upper (natCode zero) (fstT (sample p a b)) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ (num 9)
    (lower_budget a b p (GaussianNamedRealOrderTransport.precision (natCode zero) (fstT (sample p a b)) (unit p) (num 9)) hs h)

theorem original_positive_time_logarithm_below_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ le (var 0) (var 1) ⟶
      upper (fstT (sample (var 2) (var 0) (var 1))) (natCode zero) one (unit (var 2))) :=
  closeUniv 3 (.impI (.impI (original_logarithm_nonpositive _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_positive_time_logarithm_above_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ le (var 1) (var 0) ⟶
      upper (natCode zero) (fstT (sample (var 2) (var 0) (var 1))) one (unit (var 2))) :=
  closeUniv 3 (.impI (.impI (original_logarithm_nonnegative _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmSign
