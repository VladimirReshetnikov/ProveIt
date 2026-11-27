import IPRADerivations.Analysis.Gamma.Taylor.ExponentCoefficients.GaussianGammaExponentCoefficientPolynomial
import IPRADerivations.Analysis.Gamma.Zeta.Coefficients.GaussianGammaZetaTailSeries
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallPerturbationTransport

/-!
# A regular exponent name with the original shared coefficient precision

The original gamma and reciprocal-power coefficients use one explicitly
computed precision, independent of the evaluation query. The actual
finite polynomial evaluator is normalized with its proved raw modulus
R+1. Every normalized observation is still exactly one actual original
coefficient-buffer evaluation. Compatibility with the separately retimed
canonical C7 exponent name is a subsequent obligation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaSynchronousExponentName

open_ipra
open GaussianRationalHorner (qadd qmul ofGaussian evaluate)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianRationalMetric (bounded distanceBounded qnegative)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum)
open GaussianGammaCanonicalExponent (source tail_source)
open GaussianGammaCanonicalExponentBound (numericalRadius)
open GaussianGammaLinearCoefficient (coefficient)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_at_earlier_precisions)
open GaussianEuclideanDistanceName (pointCN)
open RationalGaussianEmbedding (embed)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gammaClock (p R : PTm n) : PTm n := GaussianGammaZetaDegreeName.clock (succ p) R
def linearValue (p z R B : PTm n) : PTm n := qmul (coefficient (gammaClock p R) (two*R)) (ofGaussian z B)
def rawValue (p z R B : PTm n) : PTm n := qadd (linearValue p z R B) (GaussianGammaZetaTailSeries.sample p z R B (two*R))
def rawData (z R B : PTm n) : PTm n := pairT z (pairT R B)
def rawF : PR 2 := PTm.toPR (rawValue (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)
def clock (p R : PTm n) : PTm n := GaussianFastValueCut.exponent (R+one) p
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (z R B : PTm n) : PTm n := GaussianFastValueCut.nameData (R+one) (rawData z R B)
def sample (p z R B : PTm n) : PTm n := ap2 nameF p (data z R B)
ipra_subst gammaClock
ipra_subst linearValue
ipra_subst rawValue [GaussianGammaZetaTailSeries.sample]
ipra_subst rawData
ipra_subst clock
ipra_subst data

theorem gamma_clock_later (p R : PTm n) : Γ ⊢[PRAAx] le p (gammaClock p R) :=
  le_of_eq_add (d := R*R+num 7) (by unfold gammaClock GaussianGammaZetaDegreeName.clock; ipra_ring)

/-- Arbitrary later queries of the ORIGINAL gamma name retain the original
two-precision radius after exact natural denominator clearing. -/
theorem gamma_later_distance (s t a b : PTm n) (ha : Γ ⊢[PRAAx] le s a) (hb : Γ ⊢[PRAAx] le t b) : Γ ⊢[PRAAx]
    distanceBounded (embed (GammaEulerConstantName.gammaSample a zero)) (embed (GammaEulerConstantName.gammaSample b zero))
      (unit s+unit t) (unit s*unit t) := by
  have old := distance_congr (Γ := Γ) (GaussianGammaCanonicalExponent.gamma_sample_at a) (GaussianGammaCanonicalExponent.gamma_sample_at b)
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.point_at GaussianGammaCanonicalExponent.gammaF zero a b GaussianGammaCanonicalExponent.gamma_regular)
  exact distance_at_earlier_precisions s t a b ha hb old

theorem coefficient_distance (s t R N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (coefficient (gammaClock s R) N) (coefficient (gammaClock t R) N)
      (unit s+unit t) (unit s*unit t) :=
  GaussianNameRingLaws.sum_left_error _ _ (qnegative (GaussianGammaCanonicalExponent.harmonicPoint N)) _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive t))
    (gamma_later_distance s t _ _ (gamma_clock_later s R) (gamma_clock_later t R))

theorem query_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] bounded (ofGaussian z B) R one :=
  GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ h.andE₂.andE₁ (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents _ _ h.andE₂.andE₁)
    (le_congr (by ipra_ring) (by ipra_ring) h.andE₂.andE₂)

theorem coefficient_bound (q N : PTm n) : Γ ⊢[PRAAx] bounded (coefficient q N) (succ N) one :=
  GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (le_refl one) (GaussianGammaLinearCoefficient.coefficient_norm q N)

theorem linear_distance (s t z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (linearValue s z R B) (linearValue t z R B)
      (R*(unit s+unit t)) (unit s*unit t) := by
  have hD := GaussianRationalHorner.positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive t)
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.product_distance _ _ _ _ (unit s+unit t) zero (unit s*unit t) R (succ (two*R)) hD
      (coefficient_distance s t R (two*R)) (GaussianRationalPowerDifference.distance_refl_zero _ _ hD)
      (query_bound z R B h) (coefficient_bound (gammaClock t R) (two*R)))

theorem raw_regularity (s t z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (rawValue s z R B) (rawValue t z R B)
      ((R+one)*(unit s+unit t)) (unit s*unit t) :=
  bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _
      (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive t))
      (linear_distance s t z R B h)
      (GaussianNameEquivalence.point_at GaussianGammaZetaTailSeries.nameF _ s t
        (GaussianGammaZetaTailSeries.name_regular z R B (two*R) (tail_source z R B h))))

theorem raw_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    bounded (rawValue p z R B) (numericalRadius R) one := by
  have hN := GaussianGammaExponentCoefficientPolynomial.original_cutoff_positive R h.andE₁
  have lin : Γ ⊢[PRAAx] bounded (linearValue p z R B) (succ (two*R)*R) one :=
    bound_congr (.eqRefl _) (.eqRefl _) (show Γ ⊢[PRAAx] one*one ≐ one by ipra_ring)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one)
        (coefficient_bound (gammaClock p R) (two*R)) (query_bound z R B h))
  have tail := GaussianGammaZetaTailSeries.sample_bound p z R B (two*R) (tail_source z R B h)
  have joined := bounded_sum _ _ _ _ _ _ (le_refl one) hN lin tail
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (le_refl one) hN) (le_refl one)
    (le_of_eq_add (d := R*R) (by unfold numericalRadius; ipra_ring)) joined

theorem raw_value_congr {p z R B p' z' R' B' : PTm n} (hp : Γ ⊢[PRAAx] p ≐ p')
    (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R') (hB : Γ ⊢[PRAAx] B ≐ B') : Γ ⊢[PRAAx]
    rawValue p z R B ≐ rawValue p' z' R' B' := by
  ipra_congr (rawValue (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hp, hz, hR, hB]

theorem raw_at (p z R B : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (rawData z R B) ≐ rawValue p z R B := by
  simpa [rawF, rawData, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (rawValue (var 0) (var 1) (var 2) (var 3)) p ![z, R, B])

theorem raw_name_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular rawF (R+one) (rawData z R B) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  have bound := distance_congr (raw_at (var 1) _ _ _).eqSymm (raw_at (var 0) _ _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (raw_regularity (var 1) (var 0) _ _ _ hs)
  simpa only [GaussianFastValueCut.regular,Syn.shift,subst_rawData,PTm.subst_add,PTm.subst_succ,PTm.subst_zero,unit] using bound

theorem name_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN nameF (data z R B) :=
  GaussianFastValueCut.name_fast rawF (R+one) (rawData z R B) (raw_name_regular z R B h)

theorem sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] sample p z R B ≐ rawValue (clock p R) z R B :=
  (GaussianFastValueCut.name_at rawF (R+one) (rawData z R B) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p R) z R B)).eqTrans
      (GaussianNamedSmallPerturbationTransport.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _)))

theorem sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    bounded (sample p z R B) (numericalRadius R) one :=
  bound_congr (sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _) (raw_bound (clock p R) z R B h)

theorem raw_polynomial_binding (p z R B : PTm n) : Γ ⊢[PRAAx]
    evaluate (GaussianGammaExponentCoefficientPolynomial.polynomial (gammaClock p R) (two*R) (GaussianGammaZetaTailSeries.cutoff p R))
      (ofGaussian z B) ≐ rawValue p z R B :=
  (GaussianGammaExponentCoefficientPolynomial.original_tail_observation_binding (succ p) z R B (two*R)
    (GaussianGammaZetaTailSeries.cutoff p R)).eqTrans
      (qadd_congr (.eqRefl _) (GaussianGammaZetaTailSeries.sample_at p z R B (two*R)).eqSymm)

theorem actual_sampled_exponent_polynomial_binding (p z R B : PTm n) : Γ ⊢[PRAAx]
    evaluate (GaussianGammaExponentCoefficientPolynomial.polynomial (gammaClock (clock p R) R) (two*R)
      (GaussianGammaZetaTailSeries.cutoff (clock p R) R)) (ofGaussian z B) ≐ sample p z R B :=
  (raw_polynomial_binding (clock p R) z R B).eqTrans (sample_at p z R B).eqSymm

theorem actual_synchronous_exponent_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular _ _ _ Prf.hyp0))
theorem actual_synchronous_exponent_polynomial_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (evaluate (GaussianGammaExponentCoefficientPolynomial.polynomial (gammaClock (clock (var 0) (var 2)) (var 2)) (two*var 2)
      (GaussianGammaZetaTailSeries.cutoff (clock (var 0) (var 2)) (var 2))) (ofGaussian (var 1) (var 3)) ≐
        sample (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (actual_sampled_exponent_polynomial_binding _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaSynchronousExponentName
