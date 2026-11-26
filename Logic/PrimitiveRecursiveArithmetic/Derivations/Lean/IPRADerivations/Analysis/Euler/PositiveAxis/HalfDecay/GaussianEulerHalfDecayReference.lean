import IPRADerivations.Analysis.Euler.PositiveAxis.HalfDecay.GaussianEulerHalfDecayProduct
import IPRADerivations.Analysis.Euler.PositiveAxis.HalfDecay.GaussianEulerHalfDecayQuadrature

/-!
# Actual nonnegative scalar references for half-decay observations

The scalar is the real field of the existing positive exponential
representative at the actual negative half-time. Canonical real-axis
observations identify its embedding literally with that original
representative. The genuine original decay equivalence then compares
it with the unchanged half-decay evaluator at independent precisions.
The natural numerator, actual scalar denominator and grid-cell binding
are exposed without assuming a reference sign or evaluator identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayReference

open_ipra
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData sample_canonical sample_nonnegative)
open GaussianEulerDecayOrder (signedTime original_decay_nonnegative_representative)
open GaussianEulerIntegrandName (decayF decayData)
open RationalGaussianEmbedding (embed native)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def reference (q a b : PTm n) : PTm n := ap2 positiveF q (positiveData (signedTime a (two*b)))
def scalar (q a b : PTm n) : PTm n := fstT (reference q a b)
def numerator (q a b : PTm n) : PTm n := GaussianPositiveRealArithmetic.numerator (scalar q a b)
def denominator (q a b : PTm n) : PTm n := RationalSupMetric.denominatorOf (scalar q a b)
def scalarF : PR 3 := PTm.toPR (scalar (var 0) (var 1) (var 2))
ipra_subst reference [signedTime]
ipra_subst scalar
ipra_subst numerator [GaussianPositiveRealArithmetic.numerator, RationalSupMetric.numeratorOf]
ipra_subst denominator [RationalSupMetric.denominatorOf]

theorem scalar_at (q a b : PTm n) : Γ ⊢[PRAAx] ap3 scalarF q a b ≐ scalar q a b := by
  simpa [scalarF,ap3] using toPR_eq (Γ := Γ) (scalar (var 0) (var 1) (var 2) : PTm 3) ![q,a,b]

theorem reference_embedding (q a b : PTm n) : Γ ⊢[PRAAx] reference q a b ≐ embed (scalar q a b) :=
  (RationalGaussianEmbedding.canonical_axis_roundtrip _ (sample_canonical _ q) (sample_nonnegative _ q).andE₁).eqSymm

theorem scalar_nonnegative (q a b : PTm n) : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.sign (scalar q a b) :=
  (sample_nonnegative (signedTime a (two*b)) q).andE₂

theorem scalar_canonical (q a b : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (scalar q a b) :=
  (sample_canonical (signedTime a (two*b)) q).andE₂.andE₁

theorem denominator_positive (q a b : PTm n) : Γ ⊢[PRAAx] le one (denominator q a b) :=
  RationalArgmin.denominator_positive _

theorem scalar_representation (q a b : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (scalar q a b) (ZT.ofNat (numerator q a b)) (denominator q a b) :=
  GaussianPositiveRealArithmetic.natural_representation _ (scalar_nonnegative q a b)

theorem reference_representation (q a b : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents (reference q a b) (native (ZT.ofNat (numerator q a b))) (denominator q a b) :=
  GaussianRationalHorner.represents_congr (reference_embedding q a b).eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (scalar_representation q a b))

theorem reference_norm (q a b : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (embed (scalar q a b)) (numerator q a b) (denominator q a b) := by
  have hD := denominator_positive (Γ := Γ) q a b
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (native (ZT.ofNat (numerator q a b))) ≐
      numerator q a b*numerator q a b := by
    simpa [native,GaussianDominantPairAlgebra.radiusNumerator] using
      GaussianDominantPairAlgebra.radius_numerator_norm (Γ := Γ) (numerator q a b)
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hD hD
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (scalar_representation q a b))
  have cleared : Γ ⊢[PRAAx]
      (denominator q a b*denominator q a b)*ComplexLogarithmRemainder.normSq (native (ZT.ofNat (numerator q a b))) ≐
        (numerator q a b*numerator q a b)*(denominator q a b*denominator q a b) :=
    (congrMul (.eqRefl (denominator q a b*denominator q a b)) norm).eqTrans (by ipra_ring)
  exact le_congr cleared.eqSymm (.eqRefl _) (le_refl _)

theorem decay_reference_error (q r a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    distanceBounded (embed (scalar q a b)) (ap2 decayF r (decayData a (two*b)))
      (unit q+unit r) (unit q*unit r) :=
  distance_congr (reference_embedding q a b) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.cross_at positiveF decayF _ _ q r
      (original_decay_nonnegative_representative a (two*b)
        (GaussianRationalHorner.positive_product _ _ (le_succ_self one) hb)))

theorem actual_half_evaluator (r a b x : PTm n) : Γ ⊢[PRAAx]
    ap3 GaussianEulerHalfDecayQuadrature.halfF r (pairT a b) x ≐ ap2 decayF r (decayData a (two*b)) :=
  (GaussianEulerHalfDecayQuadrature.half_at r a b x).eqTrans
    (GaussianEulerDecayQuadrature.evaluator_at r a (two*b) x)

theorem embedded_reference_error (q r a b x : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    distanceBounded (embed (scalar q a b)) (ap3 GaussianEulerHalfDecayQuadrature.halfF r (pairT a b) x)
      (unit q+unit r) (unit q*unit r) :=
  distance_congr (.eqRefl _) (actual_half_evaluator r a b x).eqSymm (.eqRefl _) (.eqRefl _)
    (decay_reference_error q r a b hb)

theorem row_reference_error (i q r N a C E x : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (embed (scalar q (a*N+C*i) (E*N)))
      (inst2 (GaussianCompactRiemannName.sampleBody GaussianEulerHalfDecayQuadrature.halfF) i (GaussianCompactRiemannName.sampleData r N a C E x))
      (unit q+unit r) (unit q*unit r) :=
  distance_congr (.eqRefl _) (GaussianCompactRiemannName.sample_body_at GaussianEulerHalfDecayQuadrature.halfF i r N a C E x).eqSymm (.eqRefl _) (.eqRefl _)
    (embedded_reference_error q r _ _ x (GaussianRationalHorner.positive_product _ _ hE hN))

theorem actual_nonnegative_half_decay_scalar_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (reference (var 0) (var 1) (var 2) ≐ embed (scalar (var 0) (var 1) (var 2)) ⋏
      GaussianPositiveRealArithmetic.sign (scalar (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (reference_embedding _ _ _) (scalar_nonnegative _ _ _))
theorem actual_half_decay_scalar_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (denominator (var 0) (var 1) (var 2)) ⋏
      RationalArithmetic.represents (scalar (var 0) (var 1) (var 2)) (ZT.ofNat (numerator (var 0) (var 1) (var 2))) (denominator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (denominator_positive _ _ _) (scalar_representation _ _ _))
theorem original_half_decay_independent_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ distanceBounded (embed (scalar (var 0) (var 2) (var 3))) (ap3 GaussianEulerHalfDecayQuadrature.halfF (var 1) (pairT (var 2) (var 3)) (var 4))
      (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (embedded_reference_error _ _ _ _ _ Prf.hyp0))
theorem actual_half_decay_scalar_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 scalarF (var 0) (var 1) (var 2) ≐ scalar (var 0) (var 1) (var 2)) :=
  closeUniv 3 (scalar_at _ _ _)
theorem actual_nonnegative_half_decay_reference_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalMetric.bounded (embed (scalar (var 0) (var 1) (var 2)))
      (numerator (var 0) (var 1) (var 2)) (denominator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (reference_norm _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayReference
