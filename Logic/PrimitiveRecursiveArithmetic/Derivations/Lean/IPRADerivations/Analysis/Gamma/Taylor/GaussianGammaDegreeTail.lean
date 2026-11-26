import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaFiniteDegreeRearrangement
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalTailMetric
import IPRADerivations.Analysis.FiniteOperations.FiniteProducts.GaussianProductStability
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameArithmetic
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianCoefficientNormOrder

/-!
# Exact degree tails of the original finite canonical Gamma program

The genuine cubic Taylor remainder retains its input magnitude. On the
half disk it yields the local R²/(k² 2^(L+1)) estimate. Finite Gaussian
triangle and reciprocal-square telescoping then retain the source C18
constant for the actual degree-major rectangle after degree L+2.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDegreeTail

open_ipra
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub bounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GammaCanonicalFactors (factorNumerator factorDenominator factorDifference)

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias power_two := Common.pw_two
theorem power_three_split (X L : PTm n) : Γ ⊢[PRAAx]
    pw X (L+LogarithmRemainder.three) ≐ X*X*pw X (succ L) :=
  ((congrAp2 powF (by ipra_ring) (.eqRefl _)).eqTrans (pw_add X two (succ L))).eqTrans
    (congrMul (power_two X) (.eqRefl _))

theorem local_cross_bound (z X D L J : PTm n)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z X)
    (hh : Γ ⊢[PRAAx] le (two*X) D) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded
      (ComplexLogarithmRemainder.scale (LogarithmRemainder.three*pw D (L+LogarithmRemainder.three)) (factorDifference z D L J))
      (two*pw X (L+LogarithmRemainder.three)*factorDenominator D L*factorDenominator D (L+J)) := by
  have h := ComplexLogarithmRemainder.bounded_scale ((two*D*D)*(two*D*D))
    (ComplexLogarithmCauchy.finite_cauchy_bound z D L X J hz hh)
  have eq : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq
      (ComplexLogarithmRemainder.scale (LogarithmRemainder.three*pw D (L+LogarithmRemainder.three)) (factorDifference z D L J)) ≐
      ComplexLogarithmRemainder.normSq (ComplexLogarithmRemainder.scale ((two*D*D)*(two*D*D))
        (ComplexLogarithmRemainder.scale (LogarithmRemainder.three*pw D (L+LogarithmRemainder.three))
          (ComplexLogarithmCauchy.difference z D L J))) := by
    apply deriveNat
    have e := natEq (GammaCanonicalFactors.difference_norm (Γ := Γ) z D L J
      (LogarithmRemainder.three*pw D (L+LogarithmRemainder.three)))
    rw [e]
    simp only [ComplexLogarithmRemainder.normSq_eval,ComplexLogarithmRemainder.scale,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,
      ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]
    ring
  exact le_congr eq.eqSymm (by unfold factorDenominator; ipra_ring) h

theorem local_cubic_distance (z X D L J : PTm n)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z X)
    (hD : Γ ⊢[PRAAx] le one D) (hh : Γ ⊢[PRAAx] le (two*X) D) : Γ ⊢[PRAAx]
    distanceBounded (GammaLogarithmFactorBridge.localFactor z D (L+J)) (GammaLogarithmFactorBridge.localFactor z D L)
      (two*pw X (L+LogarithmRemainder.three)) (LogarithmRemainder.three*pw D (L+LogarithmRemainder.three)) := by
  simpa only [GammaLogarithmFactorBridge.localFactor,factorDifference,DyadicComplexLogarithm.crossDifference] using
    GaussianGammaCanonicalTailMetric.distance_of_cross (factorNumerator z D L) (factorNumerator z D (L+J))
      (factorDenominator D L) (factorDenominator D (L+J)) (two*pw X (L+LogarithmRemainder.three))
      (LogarithmRemainder.three*pw D (L+LogarithmRemainder.three))
      (GammaCanonicalFactors.factorDenominator_positive D L hD) (GammaCanonicalFactors.factorDenominator_positive D (L+J) hD)
      (positive_product _ _ (le_of_eq_add (d := two) (by ipra_ring)) (GaussianFactorBudget.power_positive _ _ hD))
      (local_cross_bound z X D L J hz hh)

theorem local_degree_coefficient (X D L : PTm n) (hh : Γ ⊢[PRAAx] le (two*X) D) : Γ ⊢[PRAAx]
    le ((two*pw X (L+LogarithmRemainder.three))*(D*D*unit (succ L)))
      ((X*X)*(LogarithmRemainder.three*pw D (L+LogarithmRemainder.three))) := by
  have hpow := pw_le_pw (succ L) hh
  have base := AnalyticNumberTheory.PhiLower.le_mul_mono
    (le_of_eq_add (d := one) (by ipra_ring) : Γ ⊢[PRAAx] le two LogarithmRemainder.three) hpow
  have scaled := AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (X*X*D*D)) base
  have ex := natEq (power_three_split (Γ := Γ) X L)
  have ed := natEq (power_three_split (Γ := Γ) D L)
  have ep := natEq (GaussianProductStability.power_product (Γ := Γ) two X (succ L))
  exact le_congr (by apply deriveNat; unfold unit; ipra_simps; rw [ex,ep]; ring)
    (by apply deriveNat; ipra_simps; rw [ed]; ring) scaled

theorem local_degree_distance (z X D L J : PTm n)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z X)
    (hD : Γ ⊢[PRAAx] le one D) (hh : Γ ⊢[PRAAx] le (two*X) D) : Γ ⊢[PRAAx]
    distanceBounded (GammaLogarithmFactorBridge.localFactor z D (L+J)) (GammaLogarithmFactorBridge.localFactor z D L)
      (X*X) (D*D*unit (succ L)) :=
  distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (le_of_eq_add (d := two) (by ipra_ring)) (GaussianFactorBudget.power_positive _ _ hD))
    (positive_product _ _ (positive_product _ _ hD hD) (unit_positive _))
    (local_degree_coefficient X D L hh) (local_cubic_distance z X D L J hz hD hh)

theorem rational_local_degree_distance (z R B k L J : PTm n)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) (hh : Γ ⊢[PRAAx] le (two*R) k) : Γ ⊢[PRAAx]
    distanceBounded (GammaLogarithmFactorBridge.localFactor z (B*k) (L+J)) (GammaLogarithmFactorBridge.localFactor z (B*k) L)
      (R*R) (k*k*unit (succ L)) := by
  have bk := positive_product _ _ hB hk
  have half : Γ ⊢[PRAAx] le (two*(R*B)) (B*k) :=
    le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl B) hh)
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ bk bk) (unit_positive _))
    (positive_product _ _ (positive_product _ _ hk hk) (unit_positive _))
    (le_of_eq_add (d := zero) (by ipra_ring)) (local_degree_distance z (R*B) (B*k) L J hz bk half)

def difference (z B N r L J : PTm n) : PTm n := qsub
  (GaussianGammaCanonicalTailFiniteSplit.gaussianSum z B N r (L+J))
  (GaussianGammaCanonicalTailFiniteSplit.gaussianSum z B N r L)
def prefixBound (z R B N L J r : PTm n) : Fm PTm n :=
  bounded (difference z B N r L J) (R*R*r) (N*(N+r)*unit (succ L))
ipra_subst difference
ipra_subst prefixBound

theorem difference_zero (z B N L J : PTm n) : Γ ⊢[PRAAx] difference z B N zero L J ≐ GaussianRationalHorner.qzero :=
  (GaussianRationalSyntheticDivision.qsub_congr (GaussianGammaCanonicalTailFiniteSplit.gaussian_sum_zero _ _ _ _)
    (GaussianGammaCanonicalTailFiniteSplit.gaussian_sum_zero _ _ _ _)).eqTrans (GaussianCoefficientNormOrder.qsub_self _)
theorem difference_succ (z B N r L J : PTm n) : Γ ⊢[PRAAx] difference z B N (succ r) L J ≐
    GaussianRationalHorner.qadd (difference z B N r L J)
      (qsub (GaussianGammaCanonicalTailFiniteSplit.term z B (succ (N+r)) (L+J))
        (GaussianGammaCanonicalTailFiniteSplit.term z B (succ (N+r)) L)) :=
  (GaussianRationalSyntheticDivision.qsub_congr (GaussianGammaCanonicalTailFiniteSplit.gaussian_sum_succ _ _ _ _ _)
    (GaussianGammaCanonicalTailFiniteSplit.gaussian_sum_succ _ _ _ _ _)).eqTrans (GaussianNameArithmetic.sum_difference _ _ _ _)

theorem prefix_denominator_positive (N r L : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (N*(N+r)*unit (succ L)) := positive_product _ _
      (positive_product _ _ hN (le_trans hN (le_add_right N r))) (unit_positive _)
theorem prefix_zero (z R B N L J : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] prefixBound z R B N L J zero :=
  GaussianRationalReciprocal.bound_congr (difference_zero z B N L J).eqSymm (by ipra_ring) (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded zero _ (prefix_denominator_positive N zero L hN))

theorem prefix_step (z R B N L J r : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N)
    (ih : Γ ⊢[PRAAx] prefixBound z R B N L J r) : Γ ⊢[PRAAx] prefixBound z R B N L J (succ r) := by
  let U := unit (succ L)
  let k := succ (N+r)
  let P := N*(N+r)*U
  let Q := k*k*U
  have pp : Γ ⊢[PRAAx] le one P := prefix_denominator_positive N r L h.andE₂.andE₁
  have qp : Γ ⊢[PRAAx] le one Q := positive_product _ _
    (positive_product _ _ (zero_lt_succ _) (zero_lt_succ _)) (unit_positive _)
  have kp : Γ ⊢[PRAAx] le (two*R) k := le_trans h.andE₂.andE₂.andE₂
    (le_trans (le_add_right N r) (le_succ_self _))
  have point := rational_local_degree_distance z R B k L J h.andE₂.andE₂.andE₁ h.andE₁ (zero_lt_succ _) kp
  have combined := GaussianRationalReciprocal.bounded_sum _ _ (R*R*r) P (R*R) Q pp qp ih point
  have enlarged := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ (R*R*succ r) (N*(N+succ r)*U)
    (positive_product _ _ pp qp) (prefix_denominator_positive N (succ r) L h.andE₂.andE₁)
    (le_of_eq_add (d := R*R*N*N*k*U*U) (by dsimp only [P,Q,k]; ipra_ring)) combined
  exact GaussianRationalReciprocal.bound_congr (difference_succ z B N r L J).eqSymm (.eqRefl _) (.eqRefl _) enlarged

theorem finite_sharp_degree_bound (z R B N r L J : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) : Γ ⊢[PRAAx]
    prefixBound z R B N L J r := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianGammaCanonicalTailName.source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have hall : Γ ⊢[PRAAx] .all (prefixBound (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N)
      (Syn.shift L) (Syn.shift J) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_zero z R B N L J h.andE₂.andE₁
    · simp only [subst_prefixBound,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact prefix_step _ _ _ _ _ _ _ hs.wk Prf.hyp0
  simpa only [subst_prefixBound,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE r

theorem finite_uniform_degree_bound (z R B N r L J : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) : Γ ⊢[PRAAx]
    bounded (difference z B N r L J) (R*R) (N*unit (succ L)) :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (prefix_denominator_positive N r L h.andE₂.andE₁)
    (positive_product _ _ h.andE₂.andE₁ (unit_positive _))
    (le_of_eq_add (d := R*R*N*N*unit (succ L)) (by ipra_ring)) (finite_sharp_degree_bound z R B N r L J h)

theorem original_finite_C18 (z R B N r L J : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaFiniteDegreeRearrangement.degreeMajor z B N r (L+J))
      (GaussianGammaFiniteDegreeRearrangement.degreeMajor z B N r L) (R*R) (N*unit (succ L)) := by
  have upper := (GaussianGammaCanonicalTailFiniteSplit.finite_value_as_sum z B N r (L+J) h.andE₁).eqSymm.eqTrans
    (GaussianGammaFiniteDegreeRearrangement.original_finite_rearrangement z B N r (L+J) h.andE₁)
  have lower := (GaussianGammaCanonicalTailFiniteSplit.finite_value_as_sum z B N r L h.andE₁).eqSymm.eqTrans
    (GaussianGammaFiniteDegreeRearrangement.original_finite_rearrangement z B N r L h.andE₁)
  exact distance_congr upper lower (.eqRefl _) (.eqRefl _) (finite_uniform_degree_bound z R B N r L J h)

/-- At degree one the truncated quadratic-and-higher polynomial is zero.
This is the remaining C18 boundary, with 2^(1-d)=1. -/
theorem first_degree_remainder (z R B N r L : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaFiniteDegreeRearrangement.degreeMajor z B N r L)
      GaussianRationalHorner.qzero (R*R) N :=
  GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_difference _ _ (R*R) N zero one h.andE₂.andE₁ (le_refl one)
      (GaussianGammaFiniteDegreeRearrangement.uniform_rearranged_bound z R B N r L h)
      (GaussianMonicResidualRadius.zero_bounded zero one (le_refl one)))

theorem original_two_radius_C18 (z R B r L J : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaFiniteDegreeRearrangement.degreeMajor z B (two*R) r (L+J))
      (GaussianGammaFiniteDegreeRearrangement.degreeMajor z B (two*R) r L) (R*R) (two*R*unit (succ L)) :=
  original_finite_C18 z R B (two*R) r L J (GaussianGammaCanonicalExponent.tail_source z R B h)

theorem returned_degree_remainder (z R B N r L J : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (sndT (GaussianGammaFiniteDegreeRearrangement.run z B N r (L+J)))
      (sndT (GaussianGammaFiniteDegreeRearrangement.run z B N r L)) (R*R) (N*unit (succ L)) :=
  distance_congr (GaussianGammaFiniteDegreeRearrangement.returned_degree_major z B N r (L+J)).eqSymm
    (GaussianGammaFiniteDegreeRearrangement.returned_degree_major z B N r L).eqSymm (.eqRefl _) (.eqRefl _)
    (original_finite_C18 z R B N r L J h)

theorem original_local_sharp_degree_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaCanonicalTailName.source (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (GammaLogarithmFactorBridge.localFactor (var 0) (var 2*var 3) (var 4+var 5))
        (GammaLogarithmFactorBridge.localFactor (var 0) (var 2*var 3) (var 4))
        (var 1*var 1) (var 3*var 3*unit (succ (var 4)))) :=
  closeUniv 6 (.impI (rational_local_degree_distance _ _ _ _ _ _ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem original_finite_sharp_degree_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianGammaCanonicalTailName.source (var 0) (var 1) (var 2) (var 3) ⟶
      prefixBound (var 0) (var 1) (var 2) (var 3) (var 5) (var 6) (var 4)) :=
  closeUniv 7 (.impI (finite_sharp_degree_bound _ _ _ _ _ _ _ Prf.hyp0))
theorem original_finite_C18_exact_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianGammaCanonicalTailName.source (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (GaussianGammaFiniteDegreeRearrangement.degreeMajor (var 0) (var 2) (var 3) (var 4) (var 5+var 6))
        (GaussianGammaFiniteDegreeRearrangement.degreeMajor (var 0) (var 2) (var 3) (var 4) (var 5))
        (var 1*var 1) (var 3*unit (succ (var 5)))) :=
  closeUniv 7 (.impI (original_finite_C18 _ _ _ _ _ _ _ Prf.hyp0))
theorem original_K_two_R_C18_exact_constant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
      distanceBounded (GaussianGammaFiniteDegreeRearrangement.degreeMajor (var 0) (var 2) (two*var 1) (var 3) (var 4+var 5))
        (GaussianGammaFiniteDegreeRearrangement.degreeMajor (var 0) (var 2) (two*var 1) (var 3) (var 4))
        (var 1*var 1) (two*var 1*unit (succ (var 4)))) :=
  closeUniv 6 (.impI (original_two_radius_C18 _ _ _ _ _ _ Prf.hyp0))
theorem original_C18_degree_one_boundary_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaCanonicalTailName.source (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (GaussianGammaFiniteDegreeRearrangement.degreeMajor (var 0) (var 2) (var 3) (var 4) (var 5))
        GaussianRationalHorner.qzero (var 1*var 1) (var 3)) :=
  closeUniv 6 (.impI (first_degree_remainder _ _ _ _ _ _ Prf.hyp0))
theorem actual_returned_C18_degree_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianGammaCanonicalTailName.source (var 0) (var 1) (var 2) (var 3) ⟶
      distanceBounded (sndT (GaussianGammaFiniteDegreeRearrangement.run (var 0) (var 2) (var 3) (var 4) (var 5+var 6)))
        (sndT (GaussianGammaFiniteDegreeRearrangement.run (var 0) (var 2) (var 3) (var 4) (var 5)))
        (var 1*var 1) (var 3*unit (succ (var 5)))) :=
  closeUniv 7 (.impI (returned_degree_remainder _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDegreeTail
