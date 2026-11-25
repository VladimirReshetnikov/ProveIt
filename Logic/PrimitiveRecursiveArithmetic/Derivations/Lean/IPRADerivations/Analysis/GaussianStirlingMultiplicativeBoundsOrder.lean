import IPRADerivations.Analysis.GaussianNamedRealOrderEnvelope
import IPRADerivations.Analysis.GaussianStirlingMultiplicative
import IPRADerivations.Analysis.RationalConvexEndpointBudget

/-!
# Exponentiation of order between original real names

At each requested precision, the two input observations use one common
internal clock. Adding the known dyadic order slack to the right-hand
sample gives an exact rational comparison. The finite exponential
Lipschitz estimate removes this added slack in the output name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBoundsOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianRadiusExponentialName (data nameF inputPrecision value sample sample_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalReciprocal (bound_congr bounded_sum)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open RationalValueBounds (upper upper_congr upper_triangle upper_mono upper_of_radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "factor" => GaussianRadiusExponentialLipschitzRate.factor
local notation "RInput" => GaussianRadiusExponentialName.input

theorem fraction_real_part (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] fstT (GaussianPositiveRationalLogarithm.fraction a b) ≐ GaussianEuclideanDistanceName.fraction a b := by
  let v := ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (GaussianPositiveRationalLogarithm.fraction a b)) (ZT.ofNat a) b :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [v,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
      ring) (.eqRefl _) (GaussianRationalHorner.ofGaussian_represents v b hb).andE₁
  exact RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (GaussianRationalHorner.ofGaussian_canonical _ _ hb).andE₂.andE₁
    (RationalNormalForm.normalize_well_formed _ _ hb) rep (GaussianEuclideanDistanceName.fraction_represents _ _ hb)
    hb hb (.eqRefl _)

private theorem constant_sum (R p w : PTm n) : Γ ⊢[PRAAx] sample constantF R p w ≐
    GaussianRationalPolynomialExponential.scalarSum w (GaussianRadiusExponentialName.index R p) :=
  (sample_at constantF R p w).eqTrans (GaussianNameConjugation.scalar_sum_congr _ (constant_at _ _))

private theorem constant_query (f : PR 2) (R p x : PTm n) :
    Γ ⊢[PRAAx] sample f R p x ≐ sample constantF R p (ap2 f (inputPrecision R p) x) := by
  refine (sample_at f R p x).eqTrans (?_ : Γ ⊢[PRAAx] value f R p x ≐ _)
  refine (GaussianNameConjugation.scalar_sum_congr _ (constant_at _ _).eqSymm).eqTrans
    (sample_at constantF R p _).eqSymm

private theorem fraction_bound (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (GaussianPositiveRationalLogarithm.fraction A B) A B :=
  bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point A B hB).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radius_bounded A B hB)

set_option maxHeartbeats 1400000 in
private theorem observation (f g : PR 2) (V x y p : PTm n)
    (hf : Γ ⊢[PRAAx] RInput f V x) (hg : Γ ⊢[PRAAx] RInput g V y)
    (fr : Γ ⊢[PRAAx] realSamples f x) (gr : Γ ⊢[PRAAx] realSamples g y)
    (ho : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] upper (fstT (sample f (V+two) p x)) (fstT (sample g (V+two) p y))
      (two+two*factor (V+two)) (unit p) := by
  let R := V+two
  let t := inputPrecision R p
  let W := unit t
  let P := unit p
  let A := ap2 f t x
  let B := ap2 g t y
  let S := GaussianPositiveRationalLogarithm.fraction two W
  let Y := qadd B S
  have hw := unit_positive (Γ := Γ) t
  have hp := unit_positive (Γ := Γ) p
  have hr : Γ ⊢[PRAAx] le V R := le_add_right _ _
  have htw : Γ ⊢[PRAAx] le P W :=
    GaussianExponentialReference.unit_monotone (GaussianRadiusExponentialLipschitzRate.original_clock_later R p)
  have ar := real_sample_at f x t fr
  have br := real_sample_at g y t gr
  have sReal := GaussianStirlingNames.fraction_axis two W hw
  have yReal : Γ ⊢[PRAAx] GaussianRationalHorner.canonical Y ⋏ RationalGaussianEmbedding.axis Y :=
    .andI (GaussianRationalHorner.qadd_canonical _ _) (RationalGaussianEmbedding.axis_add _ _ br.andE₂ sReal)
  have ab := GaussianRadiusExponentialName.bounded_samples_at f V x t hf.andE₂
  have bb := GaussianRadiusExponentialName.bounded_samples_at g V y t hg.andE₂
  have arB := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hr) ab
  have brB := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) hr) bb
  have sb := fraction_bound two W hw
  have sbFixed := GaussianCoefficientNameBounds.bounded_radius_mono _ two W two one hw (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two hw)) sb
  have yb : Γ ⊢[PRAAx] bounded Y R one :=
    bound_congr (.eqRefl _) (by change Γ ⊢[PRAAx] V*one+two*one ≐ R; dsimp [R]; ipra_ring)
    (by ipra_ring) (bounded_sum B S V one two one (le_refl one) (le_refl one) bb sbFixed)
  have ineq := upper_mono _ _ _ _ two W (positive_product _ _ hw hw) (real_order_at f g x y t t ho)
    (le_of_eq_add (d := zero) (by dsimp only [W]; ipra_ring))
  have shiftOrder := RationalConvexEndpointBudget.order_of_upper (fstT A) (fstT B) two W hw ineq
  have read := (RationalGaussianRealPart.real_add B S).eqTrans
    (RationalAlgebra.add_congr (.eqRefl (fstT B)) (fraction_real_part two W hw))
  have cmp := RationalArgmin.rationalLE_congr (.eqRefl _) read.eqSymm shiftOrder
  have middle := real_order_at _ _ _ _ p p
    (GaussianSignedNameExponentialOrder.constant_real_order A Y R ar yReal arB yb cmp)
  have first := upper_mono _ _ _ _ two P (positive_product _ _ hp hp) middle
    (le_of_eq_add (d := zero) (by dsimp [P]; ipra_ring))
  have raw := (GaussianReconstructionRoots.distance_zero_iff S two W hw).andE₂.impE sb
  have difference : Γ ⊢[PRAAx] distanceBounded Y B two W :=
    distance_congr (.eqRefl _) (GaussianReciprocalHorner.qadd_zero_right B br.andE₁)
    (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance B B S qzero zero two W hw
      (GaussianRationalPowerDifference.distance_refl_zero B W hw) raw)
  have finite := GaussianRationalUniformExponentialLipschitz.scalar_sum_lipschitz Y B R two W
    (GaussianRadiusExponentialName.index R p) hw yb brB difference
  have actual := distance_congr (constant_sum R p Y).eqSymm (sample_at g R p y).eqSymm
    (.eqRefl _) (.eqRefl _) finite
  have last := upper_mono _ _ _ _ (two*factor R) P hw
    (upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hw actual))
    (by unfold GaussianRadiusExponentialLipschitzRate.factor; ipra_le (2*𝔞 (pw (num 3) R))*sl htw)
  have first' := upper_congr (congrFst (constant_query f R p x).eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _) first
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ hp hp)
    (upper_triangle _ _ _ _ _ _ _ first' last)
    (le_of_eq_add (d := zero) (by ipra_ring))

set_option maxHeartbeats 1200000 in
theorem exponential_order (f g : PR 2) (x y : PTm n)
    (fn : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x)
    (gn : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN g y)
    (fr : Γ ⊢[PRAAx] realSamples f x) (gr : Γ ⊢[PRAAx] realSamples g y)
    (ho : Γ ⊢[PRAAx] realOrder f g x y) :
    Γ ⊢[PRAAx] realOrder (nameF f) (nameF g) (exponentialInputData f x) (exponentialInputData g y) := by
  let V := U f x+U g y
  let R := V+two
  have hf := exponential_input f x fn
  have hg := exponential_input g y gn
  have fV := GaussianExponentialRadiusIndependence.input_widen f _ V x hf (le_add_right _ _)
  have gV := GaussianExponentialRadiusIndependence.input_widen g _ V y hg (le_add_left _ _)
  have fR := GaussianExponentialRadiusIndependence.input_widen f V R x fV (le_add_right _ _)
  have gR := GaussianExponentialRadiusIndependence.input_widen g V R y gV (le_add_right _ _)
  have support : Γ ⊢[PRAAx] GaussianNamedRealOrderEnvelope.envelope (nameF f) (nameF g)
      (data R x) (data R y) (two+two*factor R) := by
    refine .allI ?_
    have fs : Γ.map Fm.shift ⊢[PRAAx] RInput f (Syn.shift V) (Syn.shift x) := by
      simpa [Fm.shift,Syn.shift] using fV.shift
    have gs : Γ.map Fm.shift ⊢[PRAAx] RInput g (Syn.shift V) (Syn.shift y) := by
      simpa [Fm.shift,Syn.shift] using gV.shift
    have fsReal : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by
      simpa [Fm.shift,Syn.shift] using fr.shift
    have gsReal : Γ.map Fm.shift ⊢[PRAAx] realSamples g (Syn.shift y) := by
      simpa [Fm.shift,Syn.shift] using gr.shift
    have order : Γ.map Fm.shift ⊢[PRAAx] realOrder f g (Syn.shift x) (Syn.shift y) := by
      simpa [Fm.shift,Syn.shift] using ho.shift
    simpa [GaussianNamedRealOrderEnvelope.envelope,sample,R,Syn.shift,two] using
      observation f g (Syn.shift V) (Syn.shift x) (Syn.shift y) (var 0) fs gs fsReal gsReal order
  have result := GaussianNamedRealOrderEnvelope.order_from_envelope _ _ _ _ _
    (GaussianRadiusExponentialName.name_regular _ _ _ fR) (GaussianRadiusExponentialName.name_regular _ _ _ gR) support
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (GaussianExponentialRadiusIndependence.same_input_cross f _ R x hf fR)
    (GaussianExponentialRadiusIndependence.same_input_cross g R _ y gR hg) result

end LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBoundsOrder
