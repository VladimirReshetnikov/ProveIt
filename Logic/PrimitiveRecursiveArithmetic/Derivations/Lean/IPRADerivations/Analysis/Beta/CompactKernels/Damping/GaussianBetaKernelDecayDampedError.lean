import IPRADerivations.Analysis.Beta.CompactKernels.Damping.GaussianBetaKernelDampedRefinement
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelDomination
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayOrder
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalUpperRepresentation

/-!
# Decay-damped error of the original beta kernel

The finite relative telescope is compared with an actual nonnegative
original decay representative. All requested observations remain fixed;
only the finite dyadic refinement is auxiliary. Its genuine vanishing
error is removed at one explicit rational Euclidean gap precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelDecayDampedError

open_ipra
open GaussianBetaKernelDampedRefinement (numerator denominator later_source)
open GaussianBetaKernelRefinement (cutoff value)
open GaussianBetaKernelExponential (kernel)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData)
open GaussianEulerDecayOrder (signedTime)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def reference (q a b : PTm n) : PTm n := ap2 positiveF q (positiveData (signedTime a b))
def referenceScalar (q a b : PTm n) : PTm n := fstT (reference q a b)
def referenceNumerator (q a b : PTm n) : PTm n := GaussianPositiveRealArithmetic.numerator (referenceScalar q a b)
def referenceDenominator (q a b : PTm n) : PTm n := RationalSupMetric.denominatorOf (referenceScalar q a b)
def referenceBudget (q a b : PTm n) : PTm n := referenceNumerator q a b*unit q+num 3*referenceDenominator q a b

theorem full_source (a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    GaussianBetaKernelRefinement.source a b N :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ (le_trans (le_of_eq_add (d := a) (by ipra_ring)) h.andE₂.andE₂))

theorem reference_representation (q a b : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (referenceScalar q a b) (ZT.ofNat (referenceNumerator q a b)) (referenceDenominator q a b) :=
  GaussianPositiveRealArithmetic.natural_representation _ (GaussianRealExponentialPositiveRepresentative.sample_nonnegative (signedTime a b) q).andE₂

theorem reference_positive (q a b : PTm n) : Γ ⊢[PRAAx] le one (referenceDenominator q a b) :=
  RationalArgmin.denominator_positive _

theorem kernel_reference_upper (q a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (value a b N) (referenceScalar q a b) (num 3) (unit q) := by
  have left := RationalValueBounds.upper_congr (GaussianBetaKernelRefinement.kernel_real_part a b N (full_source a b N h))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (GaussianBetaKernelDomination.original_kernel_upper q a b N (full_source a b N h))
  have cross := GaussianNameEquivalence.cross_at positiveF decayF _ _ q q
    (GaussianEulerDecayOrder.original_decay_nonnegative_representative a b h.andE₁)
  have scalar := GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _
    (positive_product _ _ (unit_positive q) (unit_positive q)) cross
  have right := RationalValueBounds.upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _ scalar)
  have coarse := RationalValueBounds.upper_mono _ _ _ _ two (unit q)
    (positive_product _ _ (unit_positive q) (unit_positive q)) right (le_of_eq_add (d := zero) (by ipra_ring))
  apply RationalValueBounds.upper_mono _ _ _ _ (num 3) (unit q)
    (positive_product _ _ (unit_positive q) (unit_positive q))
    (RationalValueBounds.upper_triangle _ _ _ _ _ _ _ left coarse)
  exact le_of_eq_add (d := zero) (by ipra_ring)

/-- Exact natural upper fraction for every actual kernel, at one fixed
requested nonnegative decay reference q. -/
theorem kernel_reference_native (q a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    le (numerator a b N*(referenceDenominator q a b*unit q)) (referenceBudget q a b*denominator b N) := by
  let P := numerator a b N
  let Q := denominator b N
  let M := referenceNumerator q a b
  let D := referenceDenominator q a b
  let U := unit q
  let u := ZT.ofNat (U*D)*ZT.ofNat P
  let v := ZT.ofNat (U*Q)*ZT.ofNat M+ZT.ofNat (num 3*Q*D)
  have signed : Γ ⊢[PRAAx] zle u v := RationalUpperRepresentation.upper_from_representations _ _ Q D (num 3) U
    (ZT.ofNat P) (ZT.ofNat M)
    (RationalNonnegativePowers.power_represents _ _ _ (positive_product _ _ h.andE₁ h.andE₂.andE₁))
    (reference_representation q a b) (kernel_reference_upper q a b N h)
  have e := zle_toZ signed
  apply le_of_eq_add (d := monus (v.pos+u.neg) (u.pos+v.neg))
  apply deriveNat
  dsimp only [u,v] at e ⊢
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
  dsimp only [referenceBudget,P,Q,M,D,U]
  ipra_simps
  linear_combination -e

/-- The actual finite relative telescope, now bounded by a fixed true
decay reference. The original beta programs and degrees are unchanged. -/
theorem finite_damped_distance (q j a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    distanceBounded (kernel a b (cutoff N j)) (kernel a b N)
      (a*a*referenceBudget q a b) (b*b*N*referenceDenominator q a b*unit q) := by
  let K := cutoff N j
  let A := a*a*referenceBudget q a b
  let B := b*b*N*referenceDenominator q a b*unit q
  have hs := later_source a b N j h
  have baseDen := positive_product (Γ := Γ) _ _ (positive_product b b h.andE₁ h.andE₁) h.andE₂.andE₁
  have oldDen := positive_product (Γ := Γ) _ _ baseDen
    (GaussianBetaKernelDampedRefinement.denominator_positive b K h.andE₁ hs.andE₂.andE₁)
  have newDen := positive_product (Γ := Γ) _ _ (positive_product _ _ baseDen (reference_positive q a b)) (unit_positive q)
  have native := mul_le_mul_right (a*a*(b*b*N)) (kernel_reference_native q a b K hs)
  have upper := RationalValueBounds.upper_mono _ _ _ _ A B oldDen
    (GaussianBetaKernelDampedRefinement.original_finite_relative_error a b N j h)
    (le_congr (by dsimp only [GaussianBetaKernelDampedRefinement.relativeNumerator,B]; ipra_ring)
      (by dsimp only [GaussianBetaKernelDampedRefinement.relativeDenominator,A]; ipra_ring) native)
  have opposite := RationalValueBounds.upper_of_order (value a b N) (value a b K) A B
    (GaussianBetaKernelRefinement.dyadic_order a b N j (full_source a b N h))
  have raw := RationalGaussianNameEmbedding.distance_from_radius _ _ A B newDen
    (RationalValueBounds.radius_of_upper _ _ A B upper opposite)
  exact distance_congr (GaussianBetaKernelRefinement.kernel_embedding a b K (full_source a b K hs)).eqSymm
    (GaussianBetaKernelRefinement.kernel_embedding a b N (full_source a b N h)).eqSymm (.eqRefl _) (.eqRefl _) raw

def errorNumerator (p q a b N : PTm n) : PTm n :=
  a*a*referenceBudget q a b*unit p+b*b*N*referenceDenominator q a b*unit q
def errorDenominator (p q a b N : PTm n) : PTm n :=
  b*b*N*referenceDenominator q a b*unit q*unit p

theorem error_denominator_positive (p q a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    le one (errorDenominator p q a b N) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁)
    (reference_positive q a b)) (unit_positive q)) (unit_positive p)

/-- The already checked original approximation is used only to remove
the auxiliary dyadic cutoff. Its exponential constant disappears. -/
theorem cofinal_original_distance (p j a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    distanceBounded (kernel a b (cutoff N j)) (ap2 decayF p (decayData a b))
      (unit j+GaussianBetaKernelDomination.cost a*unit p) (unit j*unit p) := by
  let D := b*b*N
  let U := unit j
  let P := unit p
  let C := GaussianBetaKernelDomination.cost a
  have hs := later_source a b N j h
  have ht : Γ ⊢[PRAAx] le a (a*b) :=
    le_congr (one_mul a) (mul_comm b a) (mul_le_mul_right a h.andE₁)
  have old := GaussianBetaKernelExponential.original_decay_sample_bound p a b (cutoff N j) a hs ht
  have dp : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁
  have compare : Γ ⊢[PRAAx] le ((C*P+D*U)*(U*P)) ((U+C*P)*(D*U*P)) := by
    ipra_le (𝔞 (C*P*P*U))*sl dp
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (positive_product _ _ hs.andE₁ hs.andE₁) hs.andE₂.andE₁) (unit_positive p))
    (positive_product _ _ (unit_positive j) (unit_positive p))
    (le_congr (by dsimp only [GaussianBetaKernelExponential.errorNumerator,GaussianBetaKernelExponential.constantBound,C,GaussianBetaKernelDomination.cost,P,D,U,cutoff]; ipra_ring)
      (by dsimp only [GaussianBetaKernelExponential.errorDenominator,GaussianBetaKernelExponential.constantBound,C,GaussianBetaKernelDomination.cost,P,D,U,cutoff]; ipra_ring) compare) old

theorem cofinal_slack (p q j a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 decayF p (decayData a b)) (kernel a b N))
      (errorNumerator p q a b N) (errorDenominator p q a b N) (GaussianBetaKernelDomination.cost a) j := by
  have dp := positive_product (Γ := Γ) _ _ (unit_positive j) (unit_positive p)
  have dr := positive_product (Γ := Γ) _ _ (positive_product _ _
    (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁) (reference_positive q a b)) (unit_positive q)
  have first := distance_symmetric _ _ _ _ dp (cofinal_original_distance p j a b N h)
  have second := finite_damped_distance q j a b N h
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [errorNumerator,errorDenominator,unit]; ipra_ring)
    (by dsimp only [errorDenominator,unit]; ipra_ring)
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ dp dr first second)

/-- Exact requested observations. The only remaining rate is the
literal a²/(b²N) multiplying an actual positive decay reference at q;
the explicit errors are 3a²/(b²N) eps_q + eps_p. -/
theorem original_decay_damped_error (p q a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N) : Γ ⊢[PRAAx]
    distanceBounded (kernel a b N) (ap2 decayF p (decayData a b))
      (errorNumerator p q a b N) (errorDenominator p q a b N) := by
  have hd := error_denominator_positive p q a b N h
  have raw := GaussianRationalSlackRemoval.slack_removal_at
    (qsub (ap2 decayF p (decayData a b)) (kernel a b N))
    (errorNumerator p q a b N) (errorDenominator p q a b N) (GaussianBetaKernelDomination.cost a) hd
    (cofinal_slack p q (GaussianRationalSlackRemoval.precision
      (qsub (ap2 decayF p (decayData a b)) (kernel a b N))
      (errorNumerator p q a b N) (errorDenominator p q a b N) (GaussianBetaKernelDomination.cost a)) a b N h)
  exact distance_symmetric _ _ _ _ hd raw

theorem actual_positive_decay_reference_kernel_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianBetaKernelLogarithm.source (var 1) (var 2) (var 3) ⟶
      le (numerator (var 1) (var 2) (var 3)*(referenceDenominator (var 0) (var 1) (var 2)*unit (var 0)))
        (referenceBudget (var 0) (var 1) (var 2)*denominator (var 2) (var 3))) :=
  closeUniv 4 (.impI (kernel_reference_native _ _ _ _ Prf.hyp0))
theorem original_beta_kernel_decay_damped_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianBetaKernelLogarithm.source (var 2) (var 3) (var 4) ⟶
      distanceBounded (kernel (var 2) (var 3) (var 4)) (ap2 decayF (var 0) (decayData (var 2) (var 3)))
        (errorNumerator (var 0) (var 1) (var 2) (var 3) (var 4)) (errorDenominator (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (original_decay_damped_error _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelDecayDampedError
