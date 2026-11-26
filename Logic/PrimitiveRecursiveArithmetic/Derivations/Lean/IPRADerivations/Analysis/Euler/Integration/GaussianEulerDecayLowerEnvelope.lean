import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Exponential.GaussianPositiveExponentialMajorant
import IPRADerivations.Analysis.Exponential.GaussianPositiveExponentialOrder
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRealOrderTransport
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalTravelScaling
import IPRADerivations.Analysis.Beta.GaussianEulerBetaProductPascal

/-!
# Positive exponential samples at rational times at most two

Every actual Taylor sample of the positive exponential on this interval
is on the nonnegative real axis and is between one and nine. The
truncation index is arbitrary, so the result also covers the actual
query computed for the original reciprocal name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayLowerEnvelope

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianRationalPolynomialExponential (scalarSum scalarBody scalar_sum_zero)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalSyntheticBounds (natCode)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianPositiveRealArithmetic (positive)
open GaussianPositiveRationalExponentialDecay (expF expData positive_sample_at)
open GaussianPositiveRationalExponentialDecay (inverseData inverseQuery inverse_sample_at)
open GaussianRationalHorner (canonical positive_product)
open GaussianRationalReciprocal (reciprocal)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper)
open RationalSupMetric (denominatorOf)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem nine_power : Γ ⊢[PRAAx] pw (num 3) (two : PTm n) ≐ num 9 := by
  exact (pw_succ (num 3) one).eqTrans
    ((congrMul ((pw_succ (num 3) zero).eqTrans (congrMul (pw_zero (num 3)) (.eqRefl _)))
      (.eqRefl _)).eqTrans (by ipra_ring))

/-- All literal finite scalar sums at the original rational point are
bracketed by one and nine, without a cutoff condition. -/
theorem finite_positive_exponential_envelope (a b K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (h : Γ ⊢[PRAAx] le a (two*b)) :
    Γ ⊢[PRAAx] positive (scalarSum (radiusPoint a b) K) ⋏
      (rationalLE (fstT qone) (fstT (scalarSum (radiusPoint a b) K)) ⋏
       rationalLE (fstT (scalarSum (radiusPoint a b) K)) (natCode (num 9))) := by
  let x := radiusPoint a b
  have hx := GaussianPositiveExponentialTermBound.actual_positive_fraction a b hb
  have positiveSum := GaussianPositiveExponentialProduct.positive_scalar_sum x K hx
  have rawLower := GaussianPositiveExponentialTermBound.prefix_real_mono x one (succ K) hx (zero_lt_succ K)
  have lower := rationalLE_congr (congrFst (scalar_sum_zero x)) (.eqRefl _) rawLower
  have upperAtTwo := GaussianPositiveExponentialOrder.original_fraction_order a b two one K hb (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) h)
  have endpoint : Γ ⊢[PRAAx] radiusPoint two one ≐ naturalPoint two :=
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point two one (le_refl one)).eqSymm
  have same := congrFst (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl (succ K)) endpoint)
  have powerCode : Γ ⊢[PRAAx] natCode (pw (num 3) (two : PTm n)) ≐ natCode (num 9) :=
    GaussianPositiveExponentialMajorant.natCode_congr nine_power
  have upper := transitive (rationalLE_congr (.eqRefl _) same upperAtTwo)
    (rationalLE_congr (.eqRefl _) powerCode (GaussianPositiveExponentialMajorant.positive_real_majorant two K))
  exact .andI positiveSum (.andI lower upper)

theorem original_positive_exponential_envelope (a b j p : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (h : Γ ⊢[PRAAx] le a (two*b)) :
    Γ ⊢[PRAAx] positive (ap2 expF p (expData a b j)) ⋏
      (rationalLE (fstT qone) (fstT (ap2 expF p (expData a b j))) ⋏
       rationalLE (fstT (ap2 expF p (expData a b j))) (natCode (num 9))) := by
  have e := positive_sample_at (Γ := Γ) a b j p
  have finite := finite_positive_exponential_envelope a b (GaussianRadiusExponentialName.index (a+j) p) hb h
  exact .andI (GaussianPositiveRealArithmetic.positive_congr e.eqSymm finite.andE₁)
    (.andI (rationalLE_congr (.eqRefl _) (congrFst e).eqSymm finite.andE₂.andE₁)
      (rationalLE_congr (congrFst e).eqSymm (.eqRefl _) finite.andE₂.andE₂))

theorem original_positive_exponential_time_at_most_two_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ le (var 0) (two*var 1)) ⟶
        positive (ap2 expF (var 3) (expData (var 0) (var 1) (var 2))) ⋏
        (rationalLE (fstT qone) (fstT (ap2 expF (var 3) (expData (var 0) (var 1) (var 2)))) ⋏
         rationalLE (fstT (ap2 expF (var 3) (expData (var 0) (var 1) (var 2)))) (natCode (num 9)))) :=
  closeUniv 4 (.impI (original_positive_exponential_envelope _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

private theorem reciprocal_radius (m d : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] le d m) : Γ ⊢[PRAAx]
    reciprocal (radiusPoint m d) ≐ radiusPoint d m := by
  have hm := le_trans hd h
  have budget := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono h h
  have lower : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower (radiusPoint m d) one one := by
    apply GaussianRationalLowerBounds.lower_from_representation _ _ d one one hd (le_refl one)
      (GaussianDominantPairAlgebra.radius_represents m d hd)
    exact le_congr (by ipra_ring)
      ((GaussianDominantPairAlgebra.radius_numerator_norm m).eqSymm.eqTrans (by ipra_ring)) budget
  have norm := GaussianRationalReciprocal.norm_positive (radiusPoint m d) one (le_refl one) lower
  exact GaussianEulerBetaProductPascal.inverse_unique _ _ _
    (GaussianRationalReciprocal.reciprocal_canonical _) (GaussianRationalHorner.ofGaussian_canonical _ _ hm)
    (GaussianRationalReciprocal.reciprocal_identity _ norm)
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianRationalTravelScaling.inverse_radius m d hm hd))

private theorem decoded_positive_sample (q : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (h : Γ ⊢[PRAAx] positive q) : Γ ⊢[PRAAx]
    q ≐ radiusPoint (GaussianPositiveRealArithmetic.numerator (fstT q)) (denominatorOf (fstT q)) := by
  let m := GaussianPositiveRealArithmetic.numerator (fstT q)
  let d := denominatorOf (fstT q)
  have hd := RationalArgmin.denominator_positive (Γ := Γ) (fstT q)
  have he := RationalGaussianEmbedding.canonical_axis_roundtrip q hc h.andE₁
  have hr := RationalGaussianEmbedding.embed_from_representation _ _ _
    (GaussianPositiveRealArithmetic.natural_representation _ h.andE₂)
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (RationalGaussianEmbedding.native (ZT.ofNat m)) (GaussianDominantPairAlgebra.radiusNumerator m) :=
    GaussianRootAlgebra.equal_refl _
  exact he.eqSymm.eqTrans (GaussianRationalHorner.canonical_unique _ _ _ d
    (RationalGaussianEmbedding.embed_canonical _) (GaussianRationalHorner.ofGaussian_canonical _ _ hd)
    hd (GaussianRationalHorner.represents_congr (.eqRefl _) same (.eqRefl _) hr)
    (GaussianDominantPairAlgebra.radius_represents m d hd))

/-- A positive real observation in the interval from one to nine has
canonical reciprocal at least one ninth. -/
theorem reciprocal_lower_of_positive_envelope (q : PTm n)
    (hc : Γ ⊢[PRAAx] canonical q) (hp : Γ ⊢[PRAAx] positive q)
    (h1 : Γ ⊢[PRAAx] rationalLE (fstT qone) (fstT q))
    (h9 : Γ ⊢[PRAAx] rationalLE (fstT q) (natCode (num 9))) :
    Γ ⊢[PRAAx] rationalLE (fraction one (num 9)) (fstT (reciprocal q)) := by
  let m := GaussianPositiveRealArithmetic.numerator (fstT q)
  let d := denominatorOf (fstT q)
  have hd := RationalArgmin.denominator_positive (Γ := Γ) (fstT q)
  have hd9 : Γ ⊢[PRAAx] le one (num 9 : PTm n) := le_of_eq_add (d := num 8) (by ipra_ring)
  have rep := GaussianPositiveRealArithmetic.natural_representation (Γ := Γ) (fstT q) hp.andE₂
  have o : Γ ⊢[PRAAx] rationalLE (fstT (radiusPoint one one)) (fstT q) :=
    rationalLE_congr (congrFst (GaussianDominantPairAlgebra.radius_one (Γ := Γ))).eqSymm (.eqRefl _) h1
  have small : Γ ⊢[PRAAx] le d m := le_congr (by ipra_ring) (by ipra_ring)
    (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (GaussianPositiveExponentialOrder.radius_real_representation one one (le_refl one)) rep o)
  have large : Γ ⊢[PRAAx] le m (num 9*d) := le_congr (by ipra_ring) (.eqRefl _)
    (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      rep (GaussianRationalSyntheticBounds.natCode_represents (num 9)) h9)
  have hm := le_trans hd small
  have e := (GaussianNameReciprocal.reciprocal_congr (decoded_positive_sample q hc hp)).eqTrans
    (reciprocal_radius m d hd small)
  exact rationalLE_congr (.eqRefl _) (congrFst e).eqSymm
    (GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hd9 hm
      (fraction_represents one (num 9) hd9)
      (GaussianPositiveExponentialOrder.radius_real_representation d m hm)
      (le_congr (by ipra_ring) (by ipra_ring) large))

theorem reciprocal_samples_lower (a b p : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] le a (two*b)) :
    Γ ⊢[PRAAx] rationalLE (fraction one (num 9))
      (fstT (ap2 (GaussianNameReciprocal.nameF expF) p (inverseData a b zero))) := by
  let K := GaussianRadiusExponentialName.index (a+zero) (inverseQuery p)
  let q := scalarSum (radiusPoint a b) K
  have bound := finite_positive_exponential_envelope a b K hb h
  exact rationalLE_congr (.eqRefl _) (congrFst (inverse_sample_at a b zero p)).eqSymm
    (reciprocal_lower_of_positive_envelope q (GaussianRationalFiniteSum.sum_canonical _ _ _)
      bound.andE₁ bound.andE₂.andE₁ bound.andE₂.andE₂)

/-- The original decay observation is at least one ninth with only its
own requested observation tolerance. -/
theorem original_decay_lower (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] le a (two*b)) : Γ ⊢[PRAAx]
    upper (fraction one (num 9)) (fstT (ap2 decayF p (decayData a b))) one (unit p) := by
  let c := fraction (one : PTm n) (num 9)
  let y := fstT (ap2 decayF p (decayData a b))
  let t := GaussianNamedRealOrderTransport.precision c y (unit p) one
  have e := GaussianEulerDecayFactorBounds.original_decay_matches_reciprocal a b zero hb
  have distance := GaussianNameEquivalence.cross_at _ _ _ _ t p e
  have den := positive_product (Γ := Γ) _ _ (unit_positive t) (unit_positive p)
  have row := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ den distance)
  have bound := RationalValueBounds.upper_order_left _ _ _ _ _ (reciprocal_samples_lower a b t hb h) row
  exact GaussianNamedRealOrderTransport.remove_upper_slack c y one (unit p) one
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) bound)

theorem original_decay_time_at_most_two_lower_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 2) ⋏ le (var 1) (two*var 2)) ⟶
       upper (fraction one (num 9)) (fstT (ap2 decayF (var 0) (decayData (var 1) (var 2))))
         one (unit (var 0))) :=
  closeUniv 3 (.impI (original_decay_lower _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayLowerEnvelope
