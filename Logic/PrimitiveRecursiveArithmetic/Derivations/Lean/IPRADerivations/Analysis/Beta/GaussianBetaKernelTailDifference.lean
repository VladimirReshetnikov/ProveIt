import IPRADerivations.Analysis.Beta.GaussianBetaKernelDecayDampedError
import IPRADerivations.Analysis.Beta.GaussianBetaKernelUpperTail

/-!
# One decay factor for the kernel difference on its full support

The original finite beta kernel and the nonnegative decay reference
are compared directly on the real axis. Their difference requires
only one copy of the reference. This bound applies up to the endpoint
of the kernel, where the small-time quadratic estimate does not apply.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelTailDifference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaKernelExponential (kernel)
open GaussianBetaKernelRefinement (source kernel_positive)
open GaussianBetaKernelDecayDampedError (reference referenceScalar referenceNumerator
  referenceDenominator referenceBudget reference_positive)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper crossLeft upper_mono upper_triangle upper_of_radius radius_of_upper)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A nonnegative scalar observation is within its own value plus
any nonnegative allowance of every comparison point on its lower side. -/
private theorem upper_of_nonnegative_comparison (y z : PTm n)
    (hy : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign y)
    (hz : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign z) :
    Γ ⊢[PRAAx] upper y z (GaussianPositiveRealArithmetic.numerator y) (denominatorOf y) := by
  let D := denominatorOf y
  let E := denominatorOf z
  let M := GaussianPositiveRealArithmetic.numerator y
  have value : Γ ⊢[PRAAx] (numeratorOf y).pos ≐ (numeratorOf y).neg+M := eq_add_of_le hy
  have left : Γ ⊢[PRAAx] D*crossLeft y z ≐
      (numeratorOf z).neg*(D*D)+D*((numeratorOf y).neg+M)*E :=
    (congrMul (.eqRefl D) (congrAdd (congrMul value (.eqRefl E)) (.eqRefl _))).eqTrans (by ipra_ring)
  change Γ ⊢[PRAAx] le (D*crossLeft y z) (D*crossLeft z y+M*D*E)
  exact le_congr left.eqSymm (by unfold crossLeft D E; ipra_ring)
    (add_le_add_right (D*((numeratorOf y).neg+M)*E) (mul_le_mul_right (D*D) hz))

private theorem kernel_upper (q a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) :
    Γ ⊢[PRAAx] upper (fstT (kernel a b N)) (referenceScalar q a b) (num 3) (unit q) := by
  let U := unit q
  have near := GaussianBetaKernelUpperTail.reference_error q q a b h.andE₁
  have hU : Γ ⊢[PRAAx] le one U := unit_positive q
  have d := positive_product _ _ hU hU
  have near' := distance_radius_mono _ _ (U+U) (U*U) two U d hU
    (le_of_eq_add (d := zero) (by ipra_ring)) near
  have radius := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hU
    (distance_symmetric _ _ _ _ hU near')
  have both := upper_triangle _ _ _ one U two U
    (GaussianBetaKernelDomination.original_kernel_upper q a b N h)
    (upper_of_radius _ _ _ _ radius)
  exact upper_mono _ _ _ _ (num 3) U d both (le_of_eq_add (d := zero) (by ipra_ring))

theorem original_kernel_reference_distance (q a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) :
    Γ ⊢[PRAAx] distanceBounded (kernel a b N) (reference q a b)
      (referenceBudget q a b) (referenceDenominator q a b*unit q) := by
  let K := kernel a b N
  let Q := reference q a b
  let M := referenceNumerator q a b
  let D := referenceDenominator q a b
  let V := unit q
  let A := referenceBudget q a b
  have hD : Γ ⊢[PRAAx] le one D := reference_positive q a b
  have hV : Γ ⊢[PRAAx] le one V := unit_positive q
  have hK := kernel_positive a b N h
  have hQ := GaussianRealExponentialPositiveRepresentative.sample_nonnegative (Γ := Γ) (GaussianEulerDecayOrder.signedTime a b) q
  have first : Γ ⊢[PRAAx] upper (fstT K) (fstT Q) A (D*V) :=
    upper_mono _ _ _ _ _ _ hV (kernel_upper q a b N h)
      (le_of_eq_add (d := M*V*V) (by dsimp only [A,referenceBudget,M,D,V]; ipra_ring))
  have base : Γ ⊢[PRAAx] upper (fstT Q) (fstT K) M D :=
    upper_of_nonnegative_comparison (fstT Q) (fstT K) hQ.andE₂ hK.andE₂
  have second : Γ ⊢[PRAAx] upper (fstT Q) (fstT K) A (D*V) :=
    upper_mono _ _ _ _ _ _ hD base
      (le_of_eq_add (d := num 3*D*D) (by dsimp only [A,referenceBudget,M,D,V]; ipra_ring))
  have real := radius_of_upper _ _ _ _ first second
  exact distance_congr
    (RationalGaussianEmbedding.canonical_axis_roundtrip _
      (GaussianRationalReciprocal.power_canonical _ _) hK.andE₁)
    (RationalGaussianEmbedding.canonical_axis_roundtrip _
      (GaussianRealExponentialPositiveRepresentative.sample_canonical _ q) hQ.andE₁)
    (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ (positive_product _ _ hD hV) real)

def numerator (p q a b : PTm n) : PTm n :=
  (referenceNumerator q a b*unit q+num 4*referenceDenominator q a b)*unit p+
    referenceDenominator q a b*unit q
def denominator (p q a b : PTm n) : PTm n := referenceDenominator q a b*unit q*unit p

theorem original_kernel_decay_single_factor (p q a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) :
    Γ ⊢[PRAAx] distanceBounded (kernel a b N) (ap2 decayF p (decayData a b))
      (numerator p q a b) (denominator p q a b) := by
  let D := referenceDenominator q a b
  let U := unit p
  let V := unit q
  have hD := reference_positive (Γ := Γ) q a b
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) q
  have hu := positive_product _ _ (positive_product _ _ hD hV) hU
  have left := distance_radius_mono _ _ _ _ (referenceBudget q a b*U) (denominator p q a b)
    (positive_product _ _ hD hV) hu
    (le_of_eq_add (d := zero) (by unfold denominator; ipra_ring))
    (original_kernel_reference_distance q a b N h)
  have right := distance_radius_mono _ _ _ _ ((V+U)*D) (denominator p q a b)
    (positive_product _ _ hV hU) hu
    (le_of_eq_add (d := zero) (by dsimp only [denominator,D,U,V]; ipra_ring))
    (GaussianBetaKernelUpperTail.reference_error q p a b h.andE₁)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [numerator,referenceBudget,D,U,V]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu left right)

theorem original_full_support_beta_kernel_difference_one_decay_factor_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 2) (var 3) (var 4) ⟶
        distanceBounded (kernel (var 2) (var 3) (var 4)) (ap2 decayF (var 0) (decayData (var 2) (var 3)))
          (numerator (var 0) (var 1) (var 2) (var 3)) (denominator (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (original_kernel_decay_single_factor _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelTailDifference
