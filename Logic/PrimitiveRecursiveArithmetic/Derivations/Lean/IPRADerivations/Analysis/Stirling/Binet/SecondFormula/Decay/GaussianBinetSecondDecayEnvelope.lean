import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceScalarMajorant
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerWeightedHalfDecay

/-!
# Positive envelopes for the original second Binet decay

The positive real representative differs from the original Gaussian
observation by at most two dyadic units. Adding that allowance gives
a scalar majorant on every original sample. On positive arguments the
existing weighted reciprocal estimate gives the inverse-linear bound
needed to extract one factor of the damping rate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayEnvelope

open_ipra
open GaussianBinetLaplaceDomination (realDecay realNumerator realDenominator nonnegative_real_radius)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayMesh (observation)
open GaussianEulerDecayOrder (signedTime original_decay_nonnegative_representative fraction_embedding)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianGammaCanonicalExponent (constantF)
open GaussianPositiveRealArithmetic (natural_representation)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qadd qmul qmul_canonical qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product power)
open GaussianRationalSumMajorant (majorized from_representation)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr)
open GaussianReciprocalHorner (qadd_zero_right qmul_associative)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData sample_nonnegative sample_canonical)
open RationalGaussianEmbedding (embed canonical_axis_roundtrip)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "frac" => GaussianPositiveRationalLogarithm.fraction

def envelope (p a b : PTm n) : PTm n :=
  RationalArithmetic.add (fstT (realDecay p a b)) (fraction two (unit p))

ipra_subst envelope [realDecay, signedTime, two]

theorem fraction_majorized (x A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] bounded x A B) : Γ ⊢[PRAAx] majorized x (fraction A B) :=
  GaussianRationalSumMajorant.fraction_majorized x A B hB h

private theorem representative_error (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (realDecay p a b) (observation a b p) two (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring))
    (GaussianNameEquivalence.cross_at positiveF decayF (positiveData (signedTime a b)) (decayData a b) p p
      (original_decay_nonnegative_representative a b hb))

theorem decay_majorized (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] majorized (observation a b p) (envelope p a b) := by
  let v := realDecay p a b
  let M := realNumerator v
  let E := realDenominator v
  let U := unit p
  have he : Γ ⊢[PRAAx] le one E := RationalArgmin.denominator_positive _
  have hu := unit_positive (Γ := Γ) p
  have nonnegative := sample_nonnegative (Γ := Γ) (signedTime a b) p
  have canonical := sample_canonical (Γ := Γ) (signedTime a b) p
  have base : Γ ⊢[PRAAx] bounded v M E :=
    nonnegative_real_radius v M E nonnegative canonical he (le_congr (.eqRefl _) (mul_comm E M) (le_refl _))
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents (envelope p a b)
      (ZT.ofNat (M*U+two*E)) (E*U) := by
    have sum := RationalRepresentations.represents_add (fstT v) (fraction two U) (ZT.ofNat M) (ZT.ofNat two) E U
      (natural_representation _ nonnegative.andE₂) (fraction_represents two U hu)
    apply GaussianRationalHorner.scalar_congr (.eqRefl _) _ (.eqRefl _) sum
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
    ipra_simps
  have near := distance_symmetric _ _ _ _ hu (representative_error p a b hb)
  have hBound :=
    GaussianReconstructionRoots.norm_from_distance _ _ two U M E hu he near base
  have den : Γ ⊢[PRAAx] le one (E*U) := positive_product _ _ he hu
  exact from_representation _ _ _ _ den (GaussianRationalL1.nonnegative_of_representation _ _ _ den rep) rep
    (bound_congr (.eqRefl _) (by ipra_ring) (mul_comm U E) hBound)

theorem envelope_distance (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded (embed (envelope p a b)) (observation a b p) (num 4) (unit p) := by
  let v := realDecay p a b
  let U := unit p
  let w := frac two U
  have hu := unit_positive (Γ := Γ) p
  have pos := sample_nonnegative (Γ := Γ) (signedTime a b) p
  have can := sample_canonical (Γ := Γ) (signedTime a b) p
  have read : Γ ⊢[PRAAx] embed (envelope p a b) ≐ qadd v w :=
    (RationalGaussianEmbedding.embed_add _ _).eqTrans
      (qadd_congr (canonical_axis_roundtrip v can pos.andE₁) (fraction_embedding two U hu))
  have close := GaussianNameArithmetic.sum_distance v v w qzero zero two U hu
    (GaussianRationalPowerDifference.distance_refl_zero v U hu)
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hu).iffMpr
      (GaussianBinetLaplaceScalarMajorant.fraction_norm two U hu))
  have near : Γ ⊢[PRAAx] distanceBounded (embed (envelope p a b)) v two U :=
    distance_congr read.eqSymm (qadd_zero_right v can) (by ipra_ring) (.eqRefl _) close
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu near (representative_error p a b hb))

/-- For any positive rational s/b, the actual decay observation at a
sufficient clock has radius 2b/s. -/
theorem inverse_linear (p s b : PTm n) (hs : Γ ⊢[PRAAx] le one s) (hb : Γ ⊢[PRAAx] le one b)
    (hclock : Γ ⊢[PRAAx] le (two*s) (unit p)) :
    Γ ⊢[PRAAx] bounded (observation s b p) (two*b) s := by
  let U := unit p
  let a := two*s
  let z := observation s b p
  let f := frac a b
  let g := frac b a
  let r := GaussianDominantPairAlgebra.radiusPoint a b
  have h2 : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have ha : Γ ⊢[PRAAx] le one a := positive_product _ _ h2 hs
  have hp := unit_positive (Γ := Γ) p
  have hr : Γ ⊢[PRAAx] GaussianRationalHorner.canonical r :=
    GaussianRationalHorner.ofGaussian_canonical _ _ hb
  have ef : Γ ⊢[PRAAx] power r one ≐ f :=
    (GaussianRationalPowerAlgebra.power_one r hr).eqTrans
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb).eqSymm
  have factOne : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl _)).eqTrans (one_mul _))
  have numEq : Γ ⊢[PRAAx] unit one*fact one*U+two*pw a one ≐ two*U+two*a :=
    congrAdd (congrMul (congrMul (pw_one two) factOne) (.eqRefl U)) (congrMul (.eqRefl two) (pw_one a))
      |>.eqTrans (by ipra_ring)
  have raw : Γ ⊢[PRAAx] bounded (qmul f z) (two*U+two*a) U :=
    bound_congr (qmul_congr ef (.eqRefl z)) numEq (.eqRefl U)
      (GaussianEulerDecayFactorBounds.original_half_decay_factor_bound s b one p hs hb)
  have small : Γ ⊢[PRAAx] bounded (qmul f z) (num 4) one :=
    bounded_radius_mono _ _ _ _ _ hp (le_refl one) (by dsimp only [U,a]; ipra_le 2*sl hclock) raw
  have prod := bounded_product g (qmul f z) b a (num 4) one ha (le_refl one)
    (GaussianBinetLaplaceScalarMajorant.fraction_norm b a ha) small
  have e : Γ ⊢[PRAAx] qmul g (qmul f z) ≐ z :=
    ((qmul_associative g f z).eqSymm.eqTrans
      (qmul_congr (GaussianGammaHalfEulerSquare.inverse_fraction b a hb ha) (.eqRefl z))).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical z
        (GaussianRadiusExponentialName.sample_canonical constantF _ p (decayPoint s b)))
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ ha (le_refl one)) hs
    (le_of_eq_add (d := zero) (by dsimp only [a]; ipra_ring))
    (bound_congr e (.eqRefl _) (.eqRefl _) prod)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayEnvelope
