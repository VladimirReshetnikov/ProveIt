import IPRADerivations.Analysis.Euler.Integration.Decay.CompactBounds.GaussianEulerDecayCompactLower
import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianSignedNameExponentialOrder
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalUpperRepresentation

/-!
# A uniform positive lower envelope for the actual real exponential

The genuine Euclidean input disk gives the exact signed sample lower
bound -K. Original exponential order compares with the unchanged decay
at K, whose checked finite reciprocal envelope is 3^-K. One finite scalar
gap removes only the auxiliary observation; the requested exponential
sample keeps exactly its own dyadic error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRealExponentialCompactLower

open_ipra
open GaussianSignedNameExponentialOrder (realSamples real_sample_at constant_input)
open GaussianNamedPositiveExponentialOrder (sampleOrder realOrder real_order_at scalar_coordinate_distance)
open GaussianRadiusExponentialName (input nameF data)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianEulerIntegrandName (decayPoint decayF decayData)
open GaussianRationalHorner (positive_product canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem negative_bound (K : PTm n) : Γ ⊢[PRAAx] bounded (decayPoint K one) K one :=
  GaussianRationalReciprocal.bounded_negative _ K one (le_refl one)
    (GaussianRationalReciprocal.bound_congr
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point K one (le_refl one)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded K one (le_refl one)))

theorem negative_real (K : PTm n) : Γ ⊢[PRAAx] canonical (decayPoint K one) ⋏ RationalGaussianEmbedding.axis (decayPoint K one) :=
  .andI (GaussianRationalMetric.qnegative_canonical _)
    (RationalGaussianEmbedding.axis_negative _
      (RationalGaussianEmbedding.axis_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point K one (le_refl one)).eqSymm
        (GaussianPositiveExponentialTermBound.actual_positive_fraction K one (le_refl one)).andE₁))

theorem negative_sample_order (q K : PTm n) (hc : Γ ⊢[PRAAx] canonical q) (hb : Γ ⊢[PRAAx] bounded q K one) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (decayPoint K one)) (fstT q) := by
  let u := RationalSupMetric.numeratorOf (fstT q)
  let D := RationalSupMetric.denominatorOf (fstT q)
  have zeroDist : Γ ⊢[PRAAx] distanceBounded q GaussianRationalHorner.qzero K one :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalReconstruction.qsub_zero_right q hc).eqSymm (.eqRefl _) (.eqRefl _) hb
  have zeroUpper := RationalValueBounds.upper_of_radius _ _ _ _
    (RationalValueBounds.radius_symmetric _ _ _ _ (scalar_coordinate_distance _ _ K one (le_refl one) zeroDist))
  have clean : Γ ⊢[PRAAx] upper RationalGaussianEmbedding.scalarZero (fstT q) K one :=
    RationalValueBounds.upper_congr RationalGaussianRealPart.real_zero (.eqRefl _) (.eqRefl _) (.eqRefl _) zeroUpper
  have raw := RationalRepresentations.represents_self (Γ := Γ) (fstT q)
  have signed := RationalUpperRepresentation.upper_from_representations RationalGaussianEmbedding.scalarZero (fstT q) one D K one
    (ZT.ofNat zero) u (RationalGaussianEmbedding.scalar_zero_represents one) raw clean
  have nr : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (decayPoint K one)) (-ZT.ofNat K) one :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_neg,ZT.toZ_ofNat]
      ring) (.eqRefl _)
      (GaussianRationalMetric.qnegative_represents _ _ one (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl one))).andE₁
  apply RationalArithmetic.order_of_representations _ _ _ _ one D nr raw (le_refl one) (RationalArgmin.denominator_positive _)
  have lower := zle_toZ signed
  apply zle_of_toZ (PTm.monus
    ((ZT.ofNat (one*one)*u+ZT.ofNat (K*one*D)).pos+(ZT.ofNat (one*D)*ZT.ofNat zero).neg)
    ((ZT.ofNat (one*D)*ZT.ofNat zero).pos+(ZT.ofNat (one*one)*u+ZT.ofNat (K*one*D)).neg))
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_ofNat] at lower ⊢
  ipra_simps
  linear_combination lower

theorem input_order (f : PR 2) (K x : PTm n) (hi : Γ ⊢[PRAAx] input f K x)
    (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx] sampleOrder constantF f (decayPoint K one) x := by
  refine .allI ?_
  have fs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift K) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hi.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hr.shift
  have order := negative_sample_order (ap2 f (var 0) (Syn.shift x)) (Syn.shift K)
    (real_sample_at f (Syn.shift x) (var 0) rs).andE₁
    (GaussianRadiusExponentialName.bounded_samples_at f (Syn.shift K) (Syn.shift x) (var 0) fs.andE₂)
  simpa only [sampleOrder,Syn.shift,GaussianEulerIntegrandName.subst_decayPoint,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    RationalArgmin.rationalLE_congr (congrFst (constant_at (var 0) (decayPoint (Syn.shift K) one))).eqSymm (.eqRefl _) order

theorem original_order (f : PR 2) (K x : PTm n) (hi : Γ ⊢[PRAAx] input f K x)
    (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    realOrder decayF (nameF f) (decayData K one) (data K x) := by
  have ci : Γ ⊢[PRAAx] input constantF K (decayPoint K one) := constant_input (decayPoint K one) K (negative_bound K)
  have cr : Γ ⊢[PRAAx] realSamples constantF (decayPoint K one) := by
    refine .allI ?_
    have r := negative_real (Γ := Γ.map Fm.shift) (Syn.shift K)
    have read := constant_at (Γ := Γ.map Fm.shift) (var 0) (decayPoint (Syn.shift K) one)
    simpa only [realSamples,Syn.shift,GaussianEulerIntegrandName.subst_decayPoint,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      Prf.andI (GaussianRationalHorner.canonical_congr read r.andE₁) (RationalGaussianEmbedding.axis_congr read.eqSymm r.andE₂)
  have ordered := GaussianSignedNameExponentialOrder.original_signed_name_order constantF f K (decayPoint K one) x ci hi cr hr (input_order f K x hi hr)
  have old := GaussianGammaFiniteApproximantName.exponential_input constantF (decayPoint K one) ci.andE₁
  have left := GaussianExponentialRadiusIndependence.same_input_cross constantF
    (GaussianNameBounds.U constantF (decayPoint K one)) K (decayPoint K one) old ci
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ left
    (GaussianNameEquivalence.cross_refl _ _ (GaussianRadiusExponentialName.name_regular f K x hi)) ordered

theorem original_observation_lower (f : PR 2) (p K x : PTm n) (hi : Γ ⊢[PRAAx] input f K x)
    (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    upper (GaussianEuclideanDistanceName.fraction one (pw (num 3) K)) (fstT (ap2 (nameF f) p (data K x))) one (unit p) := by
  let c := GaussianEuclideanDistanceName.fraction (one : PTm n) (pw (num 3) K)
  let y := fstT (ap2 (nameF f) p (data K x))
  let t := GaussianNamedRealOrderTransport.precision c y (unit p) two
  have lower := GaussianEulerDecayCompactLower.original_decay_lower (Γ := Γ) t K one K (le_refl one) (le_of_eq_add (d := zero) (by ipra_ring))
  have ordered := real_order_at _ _ _ _ t p (original_order f K x hi hr)
  have joined := RationalValueBounds.upper_triangle _ _ _ _ _ _ _ lower ordered
  have budget : Γ ⊢[PRAAx] GaussianNamedRealOrderTransport.upperSlack c y one (unit p) two t :=
    RationalValueBounds.upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t)
      (positive_product _ _ (unit_positive t) (unit_positive p))) joined (le_of_eq_add (d := zero) (by ipra_ring))
  exact GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ two budget

theorem actual_original_real_exponential_compact_lower_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((input f (var 1) (var 2) ⋏ realSamples f (var 2)) ⟶
      upper (GaussianEuclideanDistanceName.fraction one (pw (num 3) (var 1)))
        (fstT (ap2 (nameF f) (var 0) (data (var 1) (var 2)))) one (unit (var 0))) :=
  closeUniv 3 (.impI (original_observation_lower f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRealExponentialCompactLower
