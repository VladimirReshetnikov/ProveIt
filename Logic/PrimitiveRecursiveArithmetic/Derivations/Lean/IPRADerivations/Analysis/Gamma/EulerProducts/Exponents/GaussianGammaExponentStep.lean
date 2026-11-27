import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaCutoffName
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.Tails.GaussianGammaCanonicalTailShift
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaHarmonicIncrement
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# The actual one-step change of the original C7 exponent

Harmonic rebasing and the original first-factor tail shift are combined
at finite observations. The independently computed operation-error budget
is eliminated by the existing genuine regular-name envelope theorem.
No equality of the exponents or logarithm names is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaExponentStep

open_ipra
open GaussianRationalHorner (ofGaussian qadd qmul represents positive_product qadd_represents qmul_represents
  canonical_unique represents_congr)
open GaussianRationalMetric (qsub qsub_represents distanceBounded)
open GaussianRationalSyntheticDivision (rescale_to qadd_congr qmul_congr qsub_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameRingLaws (add_sample_error multiply_sample_error sum_left_error sum_right_error product_left_error)
open GaussianGammaCanonicalExponent (gammaF constantF differenceF differenceData productF productData harmonicPoint
  gamma_regular constant_at constant_regular difference_regular product_regular exponentF)
open GaussianGammaCanonicalTailName (source)
open GaussianGammaCutoffName (exponentPoint exponentData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRootAlgebra (equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem product_rebase_from_representations (g h r q G H R Q E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hg : Γ ⊢[PRAAx] represents g G E)
    (hh : Γ ⊢[PRAAx] represents h H E) (hr : Γ ⊢[PRAAx] represents r R E)
    (hq : Γ ⊢[PRAAx] represents q Q E) : Γ ⊢[PRAAx]
    qmul (qsub g h) q ≐ qadd (qmul (qsub g (qadd h r)) q) (qmul r q) := by
  have e2 := positive_product E E hE hE
  have left := qmul_represents _ _ _ _ _ _ hE hE (qsub_represents _ _ _ _ _ hE hg hh) hq
  have right := qadd_represents _ _ _ _ _ e2
    (qmul_represents _ _ _ _ _ _ hE hE (qsub_represents _ _ _ _ _ hE hg (qadd_represents _ _ _ _ _ hE hh hr)) hq)
    (qmul_represents _ _ _ _ _ _ hE hE hr hq)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.qadd_canonical _ _) e2 (hrv := right)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := left)
  apply equal_of_values <;> simp only [re_mul,im_mul,re_sub,im_sub,re_add,im_add] <;> ring

theorem product_rebase (g h r q : PTm n) : Γ ⊢[PRAAx]
    qmul (qsub g h) q ≐ qadd (qmul (qsub g (qadd h r)) q) (qmul r q) := by
  let E := rawDen g*rawDen h*rawDen r*rawDen q
  have he := positive_product (Γ := Γ) _ _ (positive_product _ _ (positive_product _ _ (raw_den_positive g)
    (raw_den_positive h)) (raw_den_positive r)) (raw_den_positive q)
  have hg := rescale_to g (rawGaussian g) (rawDen g) (rawDen h*rawDen r*rawDen q) E (raw_represents (Γ := Γ) g) (by unfold E; ipra_ring)
  have hh := rescale_to h (rawGaussian h) (rawDen h) (rawDen g*rawDen r*rawDen q) E (raw_represents (Γ := Γ) h) (by unfold E; ipra_ring)
  have hr := rescale_to r (rawGaussian r) (rawDen r) (rawDen g*rawDen h*rawDen q) E (raw_represents (Γ := Γ) r) (by unfold E; ipra_ring)
  have hq := rescale_to q (rawGaussian q) (rawDen q) (rawDen g*rawDen h*rawDen r) E (raw_represents (Γ := Γ) q) (by unfold E; ipra_ring)
  exact product_rebase_from_representations _ _ _ _ _ _ _ _ E he hg hh hr hq

theorem reciprocal_times_point (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (GaussianGammaHarmonicIncrement.reciprocalPoint N) (ofGaussian z B) ≐ ofGaussian z (B*succ N) := by
  have hn := zero_lt_succ (Γ := Γ) N
  have he := positive_product _ _ hn hB
  have lhs := qmul_represents _ _ _ _ _ _ hn hB
    (GaussianRationalHorner.ofGaussian_represents ComplexLogarithmRemainder.oneCode (succ N) hn)
    (GaussianRationalHorner.ofGaussian_represents z B hB)
  have rhs := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl z)
    (show Γ ⊢[PRAAx] B*succ N ≐ succ N*B by ipra_ring)
    (GaussianRationalHorner.ofGaussian_represents z (B*succ N) (positive_product _ _ hB hn))
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (positive_product _ _ hB hn)) he (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;> simp only [re_mul,im_mul,re_one,im_one] <;> ring

/-- A genuine exact finite identity from the ORIGINAL harmonic program. -/
theorem harmonic_product_step (g z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qmul (qsub g (harmonicPoint N)) (ofGaussian z B) ≐
      qadd (qmul (qsub g (harmonicPoint (succ N))) (ofGaussian z B)) (ofGaussian z (B*succ N)) :=
  (product_rebase g (harmonicPoint N) (GaussianGammaHarmonicIncrement.reciprocalPoint N) (ofGaussian z B)).eqTrans
    (qadd_congr (qmul_congr (qsub_congr (.eqRefl _) (GaussianGammaHarmonicIncrement.harmonic_point_increment N).eqSymm)
      (.eqRefl _)) (reciprocal_times_point z B N hB))

theorem harmonic_sum_step (g z B N a b : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (qmul (qsub g (harmonicPoint N)) (ofGaussian z B)) (qadd a b) ≐
      qadd (qadd (qmul (qsub g (harmonicPoint (succ N))) (ofGaussian z B)) b)
        (qadd (ofGaussian z (B*succ N)) a) :=
  (qadd_congr (harmonic_product_step g z B N hB) (GaussianReciprocalHorner.qadd_commutative a b)).eqTrans
    ((GaussianRationalSumAlgebra.qadd_associative _ _ _).eqSymm.eqTrans
      (GaussianRationalSumAlgebra.shuffle_four _ _ _ _))

def gammaSample (p : PTm n) : PTm n := ap2 gammaF p zero
def differenceCore (p N : PTm n) : PTm n := qsub (gammaSample p) (harmonicPoint N)
def core (p z R B N : PTm n) : PTm n := qadd (qmul (differenceCore p N) (ofGaussian z B))
  (GaussianGammaCanonicalTailName.point p z R B N)
def operationBudget (z R B N : PTm n) : PTm n := num 3+
  (GaussianNameArithmetic.multiplyModulus differenceF constantF (differenceData N) (ofGaussian z B)+one)+num 3*R
ipra_subst gammaSample
ipra_subst differenceCore
ipra_subst core
ipra_subst operationBudget

theorem exponent_core_distance (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (exponentPoint p z R B N) (core p z R B N) (operationBudget z R B N) (unit p) := by
  have diff : Γ ⊢[PRAAx] distanceBounded (ap2 differenceF p (differenceData N)) (differenceCore p N) (num 3) (unit p) :=
    distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p _))
      (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
      (add_sample_error gammaF constantF zero (GaussianRationalMetric.qnegative (harmonicPoint N)) p gamma_regular (constant_regular _))
  have mul0 := multiply_sample_error (Γ := Γ) differenceF constantF (differenceData N) (ofGaussian z B) p
    (difference_regular N) (constant_regular _)
  have mul1 := product_left_error _ _ _ _ _ _ _ (unit_positive p) diff
    (GaussianGammaEulerHead.fraction_disk z R B h.andE₁ h.andE₂.andE₂.andE₁)
    (GaussianGeneralFTAConstants.ceil_norm_bound (differenceCore p N))
  have mul := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at p _)) (.eqRefl _) (.eqRefl _) mul0) mul1
  have add0 := add_sample_error productF GaussianGammaCanonicalTailName.pointF (productData z B N)
    (GaussianGammaCanonicalTailName.data z R B N) p (product_regular z B N)
    (GaussianGammaCanonicalTailName.name_regular z R B N h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold operationBudget GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) add0 (sum_left_error _ _ _ _ _ (unit_positive p) mul))

theorem old_unit_budget (p A : PTm n) (hA : Γ ⊢[PRAAx] le A (num 16)) :
    Γ ⊢[PRAAx] le (A*unit p) (one*DyadicComplexLogarithm.unit p) :=
  le_congr (.eqRefl _) ((show Γ ⊢[PRAAx] num 16*unit p ≐ unit p*num 16 by ipra_ring).eqTrans
    ((GaussianLocalLogarithmName.unit_factor p).eqSymm.eqTrans (by ipra_ring)))
      (LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono hA (le_refl (unit p)))

theorem local_log_difference (p z R D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    distanceBounded (GaussianLocalLogarithmName.point p z R D)
      (qadd (ofGaussian z D) (GaussianGammaCanonicalTailMetric.localValue p z R D)) (num 6) (DyadicComplexLogarithm.unit p) := by
  have full := distance_congr (GaussianLocalLogarithmName.point_at p z R D).eqSymm
    (GammaLogarithmFactorBridge.sum_is_original_sample z D (DyadicComplexLogarithm.precision p) hD).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianLocalLogarithmName.observation_distance p z R D hD)
  have part := sum_right_error (ofGaussian z D) _ _ _ _ (GaussianLocalLogarithmName.unit_positive p)
    (GaussianGammaCanonicalTailMetric.local_rounding_distance p z R D hD)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive p) full
      (distance_symmetric _ _ _ _ (GaussianLocalLogarithmName.unit_positive p) part))

theorem core_step_distance (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (core p z R B N)
      (qadd (core p z R B (succ N)) (GaussianLocalLogarithmName.point p z (R*B) (B*succ N))) two (unit p) := by
  have tail := distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive p) (unit_positive p)
    (old_unit_budget p (num 8) (le_of_eq_add (d := num 8) (by ipra_ring)))
    (GaussianGammaCanonicalTailMetric.same_query_shift p z R B N h)
  have first := sum_right_error (qmul (differenceCore p N) (ofGaussian z B)) _ _ _ _ (unit_positive p) tail
  have exactStep := harmonic_sum_step (gammaSample p) z B N
    (GaussianGammaCanonicalTailMetric.localValue p z (R*B) (B*succ N))
    (GaussianGammaCanonicalTailName.point p z R B (succ N)) h.andE₁
  have changed := distance_congr (.eqRefl _) exactStep (.eqRefl _) (.eqRefl _) first
  have logError := distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive p) (unit_positive p)
    (old_unit_budget p (num 6) (le_of_eq_add (d := num 10) (by ipra_ring)))
    (local_log_difference p z (R*B) (B*succ N) (positive_product _ _ h.andE₁ (zero_lt_succ N)))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) changed
      (sum_right_error _ _ _ _ _ (unit_positive p) (distance_symmetric _ _ _ _ (unit_positive p) logError)))

def stepF : PR 2 := GaussianNameArithmetic.addF exponentF GaussianLocalLogarithmName.pointF
def stepData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.addData
  (exponentData z R B (succ N)) (GaussianLocalLogarithmName.data z (R*B) (B*succ N))
def stepPoint (p z R B N : PTm n) : PTm n := ap2 stepF p (stepData z R B N)
def stepBudget (z R B N : PTm n) : PTm n := operationBudget z R B N+two+
  operationBudget z R B (succ N)+GaussianNameRingLaws.three
ipra_subst stepData
ipra_subst stepPoint
ipra_subst stepBudget [GaussianNameRingLaws.three]

theorem local_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianLocalLogarithmName.source z (R*B) (B*succ N) :=
  .andI (positive_product _ _ h.andE₁ (zero_lt_succ N))
    (.andI h.andE₂.andE₂.andE₁ (GaussianGammaCanonicalTailMetric.source_local_half z R B N h))
theorem step_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN stepF (stepData z R B N) :=
  GaussianNameArithmetic.add_fast _ _ _ _
    (GaussianGammaCutoffName.exponent_regular z R B (succ N) (GaussianGammaCanonicalTailMetric.source_successor z R B N h))
    (GaussianLocalLogarithmName.name_regular z (R*B) (B*succ N) (local_source z R B N h))

/-- Every term of this finite envelope is derived from the ORIGINAL
observations and the actual operation normalizers. -/
theorem step_distance (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (exponentPoint p z R B N) (stepPoint p z R B N) (stepBudget z R B N) (unit p) := by
  have hs := GaussianGammaCanonicalTailMetric.source_successor z R B N h
  have first := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (exponent_core_distance p z R B N h) (core_step_distance p z R B N h)
  have second := sum_left_error _ _ (GaussianLocalLogarithmName.point p z (R*B) (B*succ N)) _ _ (unit_positive p)
    (distance_symmetric _ _ _ _ (unit_positive p) (exponent_core_distance p z R B (succ N) hs))
  have last := add_sample_error exponentF GaussianLocalLogarithmName.pointF
    (exponentData z R B (succ N)) (GaussianLocalLogarithmName.data z (R*B) (B*succ N)) p
    (GaussianGammaCutoffName.exponent_regular z R B (succ N) hs)
    (GaussianLocalLogarithmName.name_regular z (R*B) (B*succ N) (local_source z R B N h))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold stepBudget; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first
      (distance_triangle_same _ _ _ _ _ _ (unit_positive p) second
        (distance_symmetric _ _ _ _ (unit_positive p) last)))

theorem step_envelope (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal exponentF stepF (exponentData z R B N)
      (stepData z R B N) (stepBudget z R B N) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,exponentPoint,stepPoint,Syn.shift,
    GaussianGammaCutoffName.subst_exponentData,subst_stepData,subst_stepBudget] using
    step_distance (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

/-- E_N = E_(N+1)+log(1+z/(B(N+1))) for the actual original regular
names, at arbitrary independent observation precisions. -/
theorem exponent_step_equivalent (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent exponentF stepF (exponentData z R B N) (stepData z R B N) :=
  GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (stepBudget z R B N)
    (GaussianGammaCutoffName.exponent_regular z R B N h) (step_regular z R B N h) (step_envelope z R B N h)

theorem actual_original_harmonic_product_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ qmul (qsub (var 0) (harmonicPoint (var 3))) (ofGaussian (var 1) (var 2)) ≐
      qadd (qmul (qsub (var 0) (harmonicPoint (succ (var 3)))) (ofGaussian (var 1) (var 2)))
        (ofGaussian (var 1) (var 2*succ (var 3)))) :=
  closeUniv 4 (.impI (harmonic_product_step _ _ _ _ Prf.hyp0))
theorem actual_original_logarithm_factor_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ distanceBounded (GaussianLocalLogarithmName.point (var 0) (var 1) (var 2) (var 3))
      (qadd (ofGaussian (var 1) (var 3)) (GaussianGammaCanonicalTailMetric.localValue (var 0) (var 1) (var 2) (var 3)))
      (num 6) (DyadicComplexLogarithm.unit (var 0))) :=
  closeUniv 4 (.impI (local_log_difference _ _ _ _ Prf.hyp0))
theorem original_exponent_core_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶ distanceBounded
      (exponentPoint (var 0) (var 1) (var 2) (var 3) (var 4)) (core (var 0) (var 1) (var 2) (var 3) (var 4))
      (operationBudget (var 1) (var 2) (var 3) (var 4)) (unit (var 0))) :=
  closeUniv 5 (.impI (exponent_core_distance _ _ _ _ _ Prf.hyp0))
theorem original_exponent_step_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN stepF (stepData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (step_regular _ _ _ _ Prf.hyp0))
theorem original_exponent_step_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianValueNormalizerExtensionality.rawDiagonal exponentF stepF
        (exponentData (var 0) (var 1) (var 2) (var 3)) (stepData (var 0) (var 1) (var 2) (var 3))
        (stepBudget (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (step_envelope _ _ _ _ Prf.hyp0))
theorem original_exponent_step_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent exponentF stepF
      (exponentData (var 0) (var 1) (var 2) (var 3)) (stepData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (exponent_step_equivalent _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaExponentStep
