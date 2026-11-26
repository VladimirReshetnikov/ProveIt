import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayLowerEnvelope

/-!
# Actual original decay bounded below on every positive compact

All finite positive-exponential observations at a/b <= T lie between
one and 3^T. Their actual canonical reciprocals are at least 3^(-T).
The original independent negative exponential retains only its own
requested observation allowance after one finite scalar-gap removal.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayCompactLower

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

theorem finite_positive_envelope (a b T K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (h : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] positive (scalarSum (radiusPoint a b) K) ⋏
      (rationalLE (fstT qone) (fstT (scalarSum (radiusPoint a b) K)) ⋏
       rationalLE (fstT (scalarSum (radiusPoint a b) K)) (natCode (pw (num 3) T))) := by
  let x := radiusPoint a b
  have hx := GaussianPositiveExponentialTermBound.actual_positive_fraction a b hb
  have positiveSum := GaussianPositiveExponentialProduct.positive_scalar_sum x K hx
  have rawLower := GaussianPositiveExponentialTermBound.prefix_real_mono x one (succ K) hx (zero_lt_succ K)
  have lower := rationalLE_congr (congrFst (scalar_sum_zero x)) (.eqRefl _) rawLower
  have upperAtT := GaussianPositiveExponentialOrder.original_fraction_order a b T one K hb (le_refl one)
    (le_congr (by ipra_ring) (.eqRefl _) h)
  have endpoint : Γ ⊢[PRAAx] radiusPoint T one ≐ naturalPoint T :=
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point T one (le_refl one)).eqSymm
  have same := congrFst (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl (succ K)) endpoint)
  exact .andI positiveSum (.andI lower (transitive (rationalLE_congr (.eqRefl _) same upperAtT)
    (GaussianPositiveExponentialMajorant.positive_real_majorant T K)))

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

theorem reciprocal_lower_of_positive_envelope (q M : PTm n)
    (hM : Γ ⊢[PRAAx] le one M)
    (hc : Γ ⊢[PRAAx] canonical q) (hp : Γ ⊢[PRAAx] positive q)
    (h1 : Γ ⊢[PRAAx] rationalLE (fstT qone) (fstT q))
    (h9 : Γ ⊢[PRAAx] rationalLE (fstT q) (natCode M)) :
    Γ ⊢[PRAAx] rationalLE (fraction one M) (fstT (reciprocal q)) := by
  let m := GaussianPositiveRealArithmetic.numerator (fstT q)
  let d := denominatorOf (fstT q)
  have hd := RationalArgmin.denominator_positive (Γ := Γ) (fstT q)
  have hd9 := hM
  have rep := GaussianPositiveRealArithmetic.natural_representation (Γ := Γ) (fstT q) hp.andE₂
  have o : Γ ⊢[PRAAx] rationalLE (fstT (radiusPoint one one)) (fstT q) :=
    rationalLE_congr (congrFst (GaussianDominantPairAlgebra.radius_one (Γ := Γ))).eqSymm (.eqRefl _) h1
  have small : Γ ⊢[PRAAx] le d m := le_congr (by ipra_ring) (by ipra_ring)
    (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (GaussianPositiveExponentialOrder.radius_real_representation one one (le_refl one)) rep o)
  have large : Γ ⊢[PRAAx] le m (M*d) := le_congr (by ipra_ring) (.eqRefl _)
    (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      rep (GaussianRationalSyntheticBounds.natCode_represents M) h9)
  have hm := le_trans hd small
  have e := (GaussianNameReciprocal.reciprocal_congr (decoded_positive_sample q hc hp)).eqTrans
    (reciprocal_radius m d hd small)
  exact rationalLE_congr (.eqRefl _) (congrFst e).eqSymm
    (GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hd9 hm
      (fraction_represents one M hd9)
      (GaussianPositiveExponentialOrder.radius_real_representation d m hm)
      (le_congr (by ipra_ring) (by ipra_ring) large))

theorem reciprocal_samples_lower (a b T p : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] rationalLE (fraction one (pw (num 3) T))
      (fstT (ap2 (GaussianNameReciprocal.nameF expF) p (inverseData a b zero))) := by
  let K := GaussianRadiusExponentialName.index (a+zero) (inverseQuery p)
  let q := scalarSum (radiusPoint a b) K
  have bound := finite_positive_envelope a b T K hb h
  exact rationalLE_congr (.eqRefl _) (congrFst (inverse_sample_at a b zero p)).eqSymm
    (reciprocal_lower_of_positive_envelope q (pw (num 3) T)
      (GaussianPolynomialPerturbation.power_positive (num 3) T (zero_lt_succ two))
      (GaussianRationalFiniteSum.sum_canonical _ _ _) bound.andE₁ bound.andE₂.andE₁ bound.andE₂.andE₂)

theorem original_decay_lower (p a b T : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    upper (fraction one (pw (num 3) T)) (fstT (ap2 decayF p (decayData a b))) one (unit p) := by
  let c := fraction (one : PTm n) (pw (num 3) T)
  let y := fstT (ap2 decayF p (decayData a b))
  let t := GaussianNamedRealOrderTransport.precision c y (unit p) one
  have e := GaussianEulerDecayFactorBounds.original_decay_matches_reciprocal a b zero hb
  have distance := GaussianNameEquivalence.cross_at _ _ _ _ t p e
  have den := positive_product (Γ := Γ) _ _ (unit_positive t) (unit_positive p)
  have row := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ den distance)
  have bound := RationalValueBounds.upper_order_left _ _ _ _ _ (reciprocal_samples_lower a b T t hb h) row
  exact GaussianNamedRealOrderTransport.remove_upper_slack c y one (unit p) one
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) bound)

theorem actual_original_compact_decay_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 2) ⋏ le (var 1) (var 3*var 2)) ⟶
      upper (fraction one (pw (num 3) (var 3))) (fstT (ap2 decayF (var 0) (decayData (var 1) (var 2)))) one (unit (var 0))) :=
  closeUniv 4 (.impI (original_decay_lower _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayCompactLower
