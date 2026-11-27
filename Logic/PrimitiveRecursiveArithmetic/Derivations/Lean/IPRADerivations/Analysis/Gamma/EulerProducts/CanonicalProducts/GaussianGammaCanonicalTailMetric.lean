import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.Tails.GaussianGammaCanonicalTailFiniteSplit
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GammaLocalFactorName
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameArithmetic

/-!
# Metric transport for the original canonical Gamma tail observations

The actual independent positive denominators are retained when transporting
the original integer cross differences and quotient rounding errors to the
Gaussian-rational Euclidean metric. These lemmas are used by the first-factor
tail shift; no named tail identity is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailMetric

open_ipra
open GaussianRationalHorner (ofGaussian ofGaussian_represents represents positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianGammaCanonicalTailFiniteSplit (value)
open DyadicComplexLogarithm (unit crossDifference rounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem ofGaussian_congr {a b D E : PTm n} (ha : Γ ⊢[PRAAx] a ≐ b)
    (hD : Γ ⊢[PRAAx] D ≐ E) : Γ ⊢[PRAAx] ofGaussian a D ≐ ofGaussian b E := by
  ipra_congr (ofGaussian (var 0) (var 1) : PTm 2) with [ha, hD]

/-- The original native cross difference, with both original denominators. -/
theorem distance_of_cross (a b D E A B : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded
      (ComplexLogarithmRemainder.scale B (crossDifference a b D E)) (A*D*E)) :
    Γ ⊢[PRAAx] distanceBounded (ofGaussian b E) (ofGaussian a D) A B := by
  have he := positive_product D E hD hE
  have left := GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _
    (ofGaussian_represents b E hE) (show Γ ⊢[PRAAx] E*D ≐ D*E by ipra_ring)
  have right := GaussianRationalSyntheticDivision.rescale_to _ _ _ _ _
    (ofGaussian_represents a D hD) (show Γ ⊢[PRAAx] D*E ≐ D*E from .eqRefl _)
  have rep : Γ ⊢[PRAAx] represents
      (GaussianRationalMetric.qsub (ofGaussian b E) (ofGaussian a D))
      (crossDifference a b D E) (D*E) := by
    simpa only [crossDifference,GaussianRootAlgebra.sub] using
      GaussianRationalMetric.qsub_represents _ _ _ _ _ he left right
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ he hB rep
    (le_congr (ComplexLogarithmRemainder.normSq_scale _ _) (by ipra_ring) h)

/-- The genuine two-coordinate quotient rounder costs two units at its
actual output denominator, for every raw numerator. -/
theorem rounding_distance (p a D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (ofGaussian (rounded a D (unit p)) (unit p)) (ofGaussian a D) two (unit p) := by
  have raw := ComplexLogarithmRemainder.bounded_scale (unit p)
    (DyadicComplexLogarithm.rounding_bound a D (unit p) hD)
  exact distance_of_cross a (rounded a D (unit p)) D (unit p) two (unit p)
    hD (GaussianLocalLogarithmName.unit_positive p) (GaussianLocalLogarithmName.unit_positive p)
    (le_congr (.eqRefl _) (by ipra_ring) raw)

/-- The old tail observation is compared with its SAME computed finite
cutoff, rather than with a separately specified limiting value. -/
theorem tail_rounding_distance (p z R B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (GaussianGammaCanonicalTailName.point p z R B N)
      (value z B N (GammaCanonicalNames.count p R) (GammaCanonicalNames.degree p R)) two (unit p) := by
  have e := ofGaussian_congr (Γ := Γ) (GammaCanonicalNames.observation_compute p z R B N) (.eqRefl (unit p))
  exact distance_congr ((GaussianGammaCanonicalTailName.point_at p z R B N).eqTrans e).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (rounding_distance p (GammaCanonicalNames.sample p z R B N)
      (GammaCanonicalNames.sampleDenominator p R B N) (GammaCanonicalNames.sample_positive p R B N hB))

theorem value_cutoffs_congr (z B N : PTm n) {r s L K : PTm n}
    (hr : Γ ⊢[PRAAx] r ≐ s) (hL : Γ ⊢[PRAAx] L ≐ K) :
    Γ ⊢[PRAAx] value z B N r L ≐ value z B N s K := by
  ipra_congr (value (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [.eqRefl z, .eqRefl B, .eqRefl N, hr, hL]

/-- Increasing the original index count by one at the SAME Taylor cutoff.
Both numerical budgets are derived from the actual original schedule. -/
theorem tail_one_more_distance (p z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) :
    Γ ⊢[PRAAx] distanceBounded
      (value z B N (succ (GammaCanonicalNames.count p R)) (GammaCanonicalNames.degree p R))
      (value z B N (GammaCanonicalNames.count p R) (GammaCanonicalNames.degree p R)) one (unit p) := by
  let r := GammaCanonicalNames.count p R
  let L := GammaCanonicalNames.degree p R
  let U := pw two (GammaCanonicalNames.precision p)
  have raw := GammaCanonicalNames.joint_bound z R B N r one L zero U h.andE₂.andE₂.andE₁
    h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₂
    (GammaCanonicalNames.degree_budget p R) (GammaCanonicalNames.index_budget p R N)
  have d := distance_of_cross _ _ _ _ two U
    (GammaCanonicalFactors.tailDenominator_positive B N r L h.andE₁)
    (GammaCanonicalFactors.tailDenominator_positive B N (r+one) (L+zero) h.andE₁)
    (GammaCanonicalNames.power_positive _) raw
  have actual : Γ ⊢[PRAAx] distanceBounded
      (value z B N (succ r) L) (value z B N r L) two U :=
    distance_congr (value_cutoffs_congr z B N (by ipra_ring) (by ipra_ring)).eqSymm
      (.eqRefl _) (.eqRefl _) (.eqRefl _) d
  exact distance_radius_mono _ _ _ _ _ _ (GammaCanonicalNames.power_positive _)
    (GaussianLocalLogarithmName.unit_positive p)
    (le_congr (by ipra_ring)
      ((GammaCanonicalNames.unit_budget p).eqTrans (show Γ ⊢[PRAAx]
        pw two (GammaCanonicalNames.precision p) ≐ one*U by ipra_ring))
      (le_refl (unit p*two))) actual

def localValue (p z R D : PTm n) : PTm n := ofGaussian (GammaLocalFactorName.observation p z R D) (unit p)
ipra_subst localValue

theorem local_rounding_distance (p z R D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded (localValue p z R D)
      (GammaLogarithmFactorBridge.localFactor z D (DyadicComplexLogarithm.precision p)) two (unit p) :=
  distance_congr (ofGaussian_congr (GammaLocalFactorName.observation_compute p z R D) (.eqRefl _)).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (rounding_distance p _ _ (GammaCanonicalFactors.factorDenominator_positive _ _ hD))

/-- The old canonical local-factor observation is compared with any actual
later finite Taylor factor; the source half-disk supplies the discrepancy. -/
theorem local_cutoff_distance (p z R D L : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z R)
    (hHalf : Γ ⊢[PRAAx] le (two*R) D)
    (hL : Γ ⊢[PRAAx] le (DyadicComplexLogarithm.precision p) L) :
    Γ ⊢[PRAAx] distanceBounded (localValue p z R D)
      (GammaLogarithmFactorBridge.localFactor z D L) (num 3) (unit p) := by
  let k := monus L (DyadicComplexLogarithm.precision p)
  have raw := GammaCanonicalFactors.finite_factor_cauchy z D R (DyadicComplexLogarithm.precision p) k hz hD hHalf
  have finite := distance_of_cross _ _ _ _ one (unit p)
    (GammaCanonicalFactors.factorDenominator_positive D (DyadicComplexLogarithm.precision p) hD)
    (GammaCanonicalFactors.factorDenominator_positive D (DyadicComplexLogarithm.precision p+k) hD)
    (GaussianLocalLogarithmName.unit_positive p)
    (le_congr (.eqRefl _) (by ipra_ring) raw)
  have later := ofGaussian_congr (Γ := Γ)
    (GammaLocalFactorName.factor_numerator_congr z D (eq_add_of_le hL).eqSymm)
    (GammaLocalFactorName.factor_denominator_congr D (eq_add_of_le hL).eqSymm)
  have finite' : Γ ⊢[PRAAx] distanceBounded
      (GammaLogarithmFactorBridge.localFactor z D L)
      (GammaLogarithmFactorBridge.localFactor z D (DyadicComplexLogarithm.precision p)) one (unit p) :=
    distance_congr later (.eqRefl _) (.eqRefl _) (.eqRefl _) finite
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive p)
      (local_rounding_distance p z R D hD)
      (distance_symmetric _ _ _ _ (GaussianLocalLogarithmName.unit_positive p) finite'))

theorem source_successor (z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B (succ N) :=
  .andI h.andE₁ (.andI (le_trans h.andE₂.andE₁ (le_succ_self N))
    (.andI h.andE₂.andE₂.andE₁ (le_trans h.andE₂.andE₂.andE₂ (le_succ_self N))))

theorem source_local_half (z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) :
    Γ ⊢[PRAAx] le (two*(R*B)) (B*succ N) :=
  le_congr (by ipra_ring) (by ipra_ring)
    (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono
      (le_trans h.andE₂.andE₂.andE₂ (le_succ_self N)) (le_refl B))

theorem local_schedule_cutoff (p R : PTm n) : Γ ⊢[PRAAx]
    le (DyadicComplexLogarithm.precision p) (GammaCanonicalNames.degree p R) :=
  le_of_eq_add (d := one+GammaCanonicalNames.count p R) (by
    unfold DyadicComplexLogarithm.precision GammaCanonicalNames.degree GammaCanonicalNames.precision
    ipra_ring)

/-- The exact old observations satisfy the first-factor tail shift with
eight original rounding units. All finite cutoffs and all three original
denominators are internal to the proof. -/
theorem same_query_shift (p z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (GaussianGammaCanonicalTailName.point p z R B N)
      (GaussianRationalHorner.qadd (localValue p z (R*B) (B*succ N))
        (GaussianGammaCanonicalTailName.point p z R B (succ N))) (num 8) (unit p) := by
  have up := GaussianLocalLogarithmName.unit_positive (Γ := Γ) p
  have hD := positive_product _ _ h.andE₁ (zero_lt_succ N)
  have before := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ up
    (tail_rounding_distance p z R B N h.andE₁)
    (distance_symmetric _ _ _ _ up (tail_one_more_distance p z R B N h))
  have split := GaussianGammaCanonicalTailFiniteSplit.finite_value_first z B N
    (GammaCanonicalNames.count p R) (GammaCanonicalNames.degree p R) h.andE₁
  have first := distance_congr (.eqRefl _) split (.eqRefl _) (.eqRefl _) before
  have after := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ up
    (local_cutoff_distance p z (R*B) (B*succ N) (GammaCanonicalNames.degree p R) hD
      h.andE₂.andE₂.andE₁ (source_local_half z R B N h) (local_schedule_cutoff p R))
    (tail_rounding_distance p z R B (succ N) h.andE₁)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ up first
      (distance_symmetric _ _ _ _ up after))

theorem original_cross_metric_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ le one (var 3) ⟶ le one (var 5) ⟶
      ComplexLogarithmRemainder.bounded (ComplexLogarithmRemainder.scale (var 5)
        (crossDifference (var 0) (var 1) (var 2) (var 3))) (var 4*var 2*var 3) ⟶
      distanceBounded (ofGaussian (var 1) (var 3)) (ofGaussian (var 0) (var 2)) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (distance_of_cross _ _ _ _ _ _ (Prf.hyp0.wk.wk.wk) (Prf.hyp0.wk.wk) Prf.hyp0.wk Prf.hyp0)))))

theorem actual_quotient_rounding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ distanceBounded
      (ofGaussian (rounded (var 1) (var 2) (unit (var 0))) (unit (var 0)))
      (ofGaussian (var 1) (var 2)) two (unit (var 0))) :=
  closeUniv 3 (.impI (rounding_distance _ _ _ Prf.hyp0))

theorem actual_tail_rounding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 3) ⟶ distanceBounded (GaussianGammaCanonicalTailName.point (var 0) (var 1) (var 2) (var 3) (var 4))
      (value (var 1) (var 3) (var 4) (GammaCanonicalNames.count (var 0) (var 2))
        (GammaCanonicalNames.degree (var 0) (var 2))) two (unit (var 0))) :=
  closeUniv 5 (.impI (tail_rounding_distance _ _ _ _ _ Prf.hyp0))

theorem source_one_more_index_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGammaCanonicalTailName.source (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded
      (value (var 1) (var 3) (var 4) (succ (GammaCanonicalNames.count (var 0) (var 2)))
        (GammaCanonicalNames.degree (var 0) (var 2)))
      (value (var 1) (var 3) (var 4) (GammaCanonicalNames.count (var 0) (var 2))
        (GammaCanonicalNames.degree (var 0) (var 2))) one (unit (var 0))) :=
  closeUniv 5 (.impI (tail_one_more_distance _ _ _ _ _ Prf.hyp0))

theorem source_same_query_tail_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGammaCanonicalTailName.source (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded
      (GaussianGammaCanonicalTailName.point (var 0) (var 1) (var 2) (var 3) (var 4))
      (GaussianRationalHorner.qadd (localValue (var 0) (var 1) (var 2*var 3) (var 3*succ (var 4)))
        (GaussianGammaCanonicalTailName.point (var 0) (var 1) (var 2) (var 3) (succ (var 4))))
      (num 8) (unit (var 0))) :=
  closeUniv 5 (.impI (same_query_shift _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailMetric
