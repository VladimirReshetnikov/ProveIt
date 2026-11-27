import IPRADerivations.Analysis.Trigonometry.Cyclic.Chords.GaussianCyclicRootHalfAngle
import IPRADerivations.Analysis.Names.Arithmetic.GaussianBoundedInverseApartness

/-!
# Finite exponential product and margin estimates

Uniform sample bounds give diagonal product errors independent of the
normalizer's data-dependent clock. A squared reverse-triangle estimate
then transports finite fractional apartness through a sufficiently
small perturbation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicExponentialSamples

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedSincSamples (common_late_distance)
open GaussianNameArithmetic (multiplyF multiplyData product_distance)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianNameRingLaws (negativeF negativeData oneF one_at)
open GaussianNameEquivalence (cross_diagonal_at)
open GaussianRadiusExponentialName (input nameF data)
open GaussianExponentialInverse (negative_input exponential_inverse)
open GaussianRationalMetric (bounded distanceBounded bounded_difference_iff)
open GaussianRationalLowerBounds (lower lower_from_representation lower_to_cleared)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_radius_mono)
open GaussianRationalHorner (qmul represents represents_rescale positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalReciprocal (qone bound_congr)
open ComplexLogarithmRemainder (scale normSq)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem product_error (f g : PR 2) (x y p A B : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (fa : ∀ t : PTm n, Γ ⊢[PRAAx] bounded (ap2 f t x) A one)
    (gb : ∀ t : PTm n, Γ ⊢[PRAAx] bounded (ap2 g t y) B one) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF f g) p (multiplyData f g x y))
      (qmul (ap2 f p x) (ap2 g p y)) (two*(A+B)) (unit p) := by
  let k := productClock f g x y p
  have hk : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have left := common_late_distance f x p k p hf hk (le_refl _)
  have right := common_late_distance g y p k p hg hk (le_refl _)
  exact distance_congr (product_at f g x y p).eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (product_distance _ _ _ _ two two (unit p) B A (unit_positive p) left right (gb k) (fa p))

def sampleBound (R : PTm n) : PTm n := pw (num 3) R
def inverseBudget (R : PTm n) : PTm n := num 4*sampleBound R+two

ipra_subst sampleBound
ipra_subst inverseBudget

theorem exponential_bound (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (ap2 (nameF f) p (data R x)) (sampleBound R) one :=
  bound_congr (GaussianRadiusExponentialName.sample_at f R p x).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _ (GaussianRadiusExponentialName.query_bound f R x p h))

theorem inverse_error (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (ap2 (nameF f) p (data R x)) (ap2 (nameF (negativeF f)) p (data R (negativeData x))))
      qone (inverseBudget R) (unit p) := by
  let g := negativeF f
  let y := negativeData x
  let b := sampleBound R
  let F := nameF f
  let G := nameF g
  let a := data R x
  let d := data R y
  let X := multiplyData F G a d
  have hU := unit_positive (Γ := Γ) p
  have hg := negative_input f R x h
  have product := product_error F G a d p b b (GaussianRadiusExponentialName.name_regular _ _ _ h)
    (GaussianRadiusExponentialName.name_regular _ _ _ hg) (fun t => exponential_bound f R x t h)
    (fun t => exponential_bound g R y t hg)
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF F G) p X) qone two (unit p) :=
    distance_congr (.eqRefl _) (one_at p x) (.eqRefl _) (.eqRefl _)
      (cross_diagonal_at p (exponential_inverse f R x h))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold inverseBudget; dsimp only [b]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU (distance_symmetric _ _ _ _ hU product) near)

theorem exponential_lower (f : PR 2) (R x p : PTm n) (h : Γ ⊢[PRAAx] input f R x)
    (hp : Γ ⊢[PRAAx] le (two*inverseBudget R) (unit p)) :
    Γ ⊢[PRAAx] lower (ap2 (nameF f) p (data R x)) one (two*sampleBound R) := by
  let u := ap2 (nameF f) p (data R x)
  let v := ap2 (nameF (negativeF f)) p (data R (negativeData x))
  have near : Γ ⊢[PRAAx] distanceBounded (qmul u v) qone one two :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive p) (le_succ_self one)
      (le_congr (mul_comm _ _) (one_mul _).eqSymm hp) (inverse_error f R x p h)
  have b : Γ ⊢[PRAAx] le one (sampleBound R) :=
    RationalNonnegativePowers.denominator_positive _ _ (by ipra_le 2)
  exact GaussianBoundedInverseApartness.factor_lower u v one two (sampleBound R) (le_succ_self _) b
    (GaussianBoundedInverseApartness.lower_near_one _ near)
    (exponential_bound (negativeF f) R (negativeData x) p (negative_input f R x h))

theorem lower_under_half_error (q r A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] lower r A B) (hd : Γ ⊢[PRAAx] distanceBounded q r C D)
    (h : Γ ⊢[PRAAx] le ((two*B)*C) (A*D)) :
    Γ ⊢[PRAAx] lower q A (two*B) := by
  let L := rawDen r
  let M := rawDen q
  let E := L*M
  let v := scale M (rawGaussian r)
  let w := scale L (rawGaussian q)
  let U := two*B
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive r) (raw_den_positive q)
  have hU : Γ ⊢[PRAAx] le one U := positive_product _ _ (le_succ_self _) hB
  have vr : Γ ⊢[PRAAx] represents r v E := represents_rescale _ _ _ _ (raw_represents r)
  have qw : Γ ⊢[PRAAx] represents q w E :=
    GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _ (raw_represents q) (mul_comm _ _)
  have near : Γ ⊢[PRAAx] distanceBounded r q A U :=
    distance_radius_mono _ _ _ _ _ _ hD hU (le_congr (mul_comm _ _) (.eqRefl _) h)
      (distance_symmetric _ _ _ _ hD hd)
  have diff := (bounded_difference_iff _ _ _ _ _ _ _ hE hU vr qw).iffMp near
  have ref := lower_to_cleared _ _ _ _ _ hE hB vr hr
  have square : Γ ⊢[PRAAx] le (two*two*((A*E)*(A*E))) (U*U*normSq v) :=
    le_congr (by ipra_ring) (by dsimp only [U]; ipra_ring) (le_mul_mono (le_refl (two*two)) ref)
  exact lower_from_representation _ _ _ _ _ hE hU qw
    (le_congr (by ipra_ring) (.eqRefl _)
      (GaussianGeneralCoefficientNames.native_apart_tail v w (A*E) U square
        (le_congr (.eqRefl _) (by ipra_ring) diff)))

end LeanProofs.IPRA.Analysis.GaussianCyclicExponentialSamples
