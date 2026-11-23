import IPRADerivations.Analysis.GaussianSignedNameExponentialOrder

/-!
# Nonnegative real exponentials at unchanged independent observations

Every actual real input observation has a nonnegative exponential
representative. The original name is compared with its own constant
observation; one finite scalar gap removes that auxiliary observation.
The requested original exponential sample retains just its own error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRealNameExponentialNonnegative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSignedNameExponentialOrder (realSamples real_sample_at constant_input constant_equal_cross)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData originalData)
open GaussianRadiusExponentialName (input nameF data)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (canonical positive_product)
open GaussianRationalMetric (bounded)
open RationalGaussianEmbedding (embed scalarZero axis canonical_axis_roundtrip)
open RationalValueBounds (upper upper_of_radius upper_order_left upper_triangle upper_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cost (R : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor R+num 3

theorem zero_order (c : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign c) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (scalarZero : PTm n) c :=
  GaussianRationalMetric.comparison_of_cleared _ _ zero (GaussianPositiveRealArithmetic.numerator c) one (RationalSupMetric.denominatorOf c)
    (le_refl one) (RationalArgmin.denominator_positive c) (RationalGaussianEmbedding.scalar_zero_represents one)
    (GaussianPositiveRealArithmetic.natural_representation c h)
    (le_congr (by ipra_ring) (by ipra_ring) (zero_le _))

theorem constant_positive_cross (R q : PTm n)
    (hq : Γ ⊢[PRAAx] canonical q ⋏ axis q) (hb : Γ ⊢[PRAAx] bounded q R one) : Γ ⊢[PRAAx]
    crossEquivalent (nameF constantF) positiveF (data R q) (positiveData (fstT q)) := by
  let c := fstT q
  have eq := canonical_axis_roundtrip q hq.andE₁ hq.andE₂
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper constantF constantF R
    (GaussianNameBounds.U constantF (embed c)) q (embed c) (constant_input q R hb)
    (exponential_input constantF (embed c) (constant_regular _)) (constant_equal_cross q (embed c) eq.eqSymm)
  exact cross_trans _ _ _ _ _ _ proper
    (cross_symm _ _ _ _ (GaussianRealExponentialPositiveRepresentative.original_signed_real_exponential c))

theorem auxiliary_lower (f : PR 2) (R x p j : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack scalarZero (fstT (ap2 (nameF f) p (data R x))) one (unit p) (cost R) j := by
  let c := ap2 f j x
  let F := ap2 (nameF f) p (data R x)
  let C := ap2 (nameF constantF) j (data R c)
  let P := ap2 positiveF j (positiveData (fstT c))
  let A := rateNumerator (GaussianRadiusExponentialLipschitzRate.factor R*one) (unit j) p j
  let D := rateDenominator (unit j) p j
  have hd := GaussianNamedInverseRate.denominator_positive (Γ := Γ) (unit j) p j (unit_positive j)
  have hj := positive_product (Γ := Γ) _ _ (unit_positive j) (unit_positive j)
  have first := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance F C A D hd
    (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p j (GaussianSignedNameExponentialOrder.exponential_own_sample_rate f R x j hf))
  have near := cross_at (nameF constantF) positiveF (data R c) (positiveData (fstT c)) j j
    (constant_positive_cross R c (real_sample_at f x j hr) (GaussianRadiusExponentialName.bounded_samples_at f R x j hf.andE₂))
  have second := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance C P (unit j+unit j) (unit j*unit j) hj near
  have combined := upper_triangle (fstT P) (fstT C) (fstT F) (unit j+unit j) (unit j*unit j) A D
    (upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ second))
    (upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ first))
  have lower := upper_order_left scalarZero (fstT P) (fstT F) _ _
    (zero_order (fstT P) (GaussianRealExponentialPositiveRepresentative.sample_nonnegative (fstT c) j).andE₂) combined
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ hj hd) lower
  exact le_of_eq_add (d := zero) (by
    dsimp only [A,D,rateNumerator,rateDenominator,cost]
    ipra_ring)

theorem original_observation_nonnegative (f : PR 2) (R x p : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    upper scalarZero (fstT (ap2 (nameF f) p (data R x))) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ (cost R)
    (auxiliary_lower f R x p (GaussianNamedRealOrderTransport.precision scalarZero
      (fstT (ap2 (nameF f) p (data R x))) (unit p) (cost R)) hf hr)

theorem original_real_name_exponential_nonnegative_observation_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((input f (var 0) (var 1) ⋏ realSamples f (var 1)) ⟶
        upper scalarZero (fstT (ap2 (nameF f) (var 2) (data (var 0) (var 1)))) one (unit (var 2))) :=
  closeUniv 3 (.impI (original_observation_nonnegative f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRealNameExponentialNonnegative
