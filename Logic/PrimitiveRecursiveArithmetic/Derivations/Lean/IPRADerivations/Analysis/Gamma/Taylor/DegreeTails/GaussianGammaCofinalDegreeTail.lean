import IPRADerivations.Analysis.Gamma.Taylor.DegreeTails.GaussianGammaFixedDegreeHorizon
import IPRADerivations.Analysis.Gamma.Taylor.DegreeTails.GaussianGammaDegreeTail
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalTailMetric
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# Exact C18 between the original canonical tail and a fixed-degree name

The two actual names are compared through the SAME original joint finite
sample at an arbitrarily late precision. Finite C18 contributes precisely
R²/(N 2^(L+1)); actual quotient rounding and the two name comparisons
contribute four auxiliary dyadic errors, removed by finite rational slack.
Only the two independently requested observation errors remain.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCofinalDegreeTail

open_ipra
open GaussianGammaCanonicalTailName (source point)
open GaussianGammaFixedDegreeHorizon (observation)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNamedInverseRate (rateNumerator rateDenominator independentRate denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rateDen (N L : PTm n) : PTm n := N*unit (succ L)
ipra_subst rateDen
theorem rate_den_positive (N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (rateDen N L) :=
  positive_product _ _ hN (unit_positive _)

theorem degree_major_degree_congr (z B N r : PTm n) {L K : PTm n} (he : Γ ⊢[PRAAx] L ≐ K) : Γ ⊢[PRAAx]
    GaussianGammaFiniteDegreeRearrangement.degreeMajor z B N r L ≐ GaussianGammaFiniteDegreeRearrangement.degreeMajor z B N r K :=
  GaussianRationalFiniteSum.sum_index_congr _ (congrSucc he) (.eqRefl _)

theorem original_joint_to_fixed_degree (u z R B N L : PTm n)
    (h : Γ ⊢[PRAAx] source z R B N) (hL : Γ ⊢[PRAAx] le L (GammaCanonicalNames.degree u R)) : Γ ⊢[PRAAx]
    distanceBounded (point u z R B N) (observation u z R B N L)
      ((R*R)*unit u+two*rateDen N L) (rateDen N L*unit u) := by
  let K := GammaCanonicalNames.degree u R
  let r := GammaCanonicalNames.count u R
  have vp := rate_den_positive N L h.andE₂.andE₁
  have rounding := distance_congr (.eqRefl _)
    (GaussianGammaFiniteDegreeRearrangement.original_finite_rearrangement z B N r K h.andE₁)
    (.eqRefl _) (.eqRefl _) (GaussianGammaCanonicalTailMetric.tail_rounding_distance u z R B N h.andE₁)
  have finite := distance_congr (degree_major_degree_congr z B N r (eq_add_of_le hL).eqSymm)
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianGammaDegreeTail.original_finite_C18 z R B N r L (LeanProofs.IPRA.PTm.monus K L) h)
  have grow : Γ ⊢[PRAAx] le (unit u) (DyadicComplexLogarithm.unit u) :=
    GaussianFactorBudget.power_monotone_length two u _ (le_succ_self one) (le_add_right _ _)
  have coarse := distance_radius_mono _ _ two (DyadicComplexLogarithm.unit u) two (unit u)
    (GaussianFactorBudget.power_positive _ _ (le_succ_self one)) (unit_positive u)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl two) grow) rounding
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive u) vp coarse finite
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _) joined

theorem auxiliary_slack (p q u z R B N L : PTm n)
    (h : Γ ⊢[PRAAx] source z R B N) (hL : Γ ⊢[PRAAx] le L (GammaCanonicalNames.degree u R)) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (point p z R B N) (observation q z R B N L))
      (rateNumerator (R*R) (rateDen N L) p q) (rateDenominator (rateDen N L) p q) (two*two) u := by
  let V := rateDen N L
  let Z := rateDenominator V p q*unit u
  have vp := rate_den_positive N L h.andE₂.andE₁
  have zp : Γ ⊢[PRAAx] le one Z := positive_product _ _ (denominator_positive V p q vp) (unit_positive u)
  have first := distance_radius_mono _ _ (unit p+unit u) (unit p*unit u) ((unit p+unit u)*(V*unit q)) Z
    (positive_product _ _ (unit_positive p) (unit_positive u)) zp
    (le_of_eq_add (d := zero) (by dsimp only [Z,rateDenominator]; ipra_ring))
    (GaussianGammaCanonicalTailName.point_regularity p u z R B N h)
  have middle := distance_radius_mono _ _ ((R*R)*unit u+two*V) (V*unit u) (((R*R)*unit u+two*V)*(unit p*unit q)) Z
    (positive_product _ _ vp (unit_positive u)) zp
    (le_of_eq_add (d := zero) (by dsimp only [Z,rateDenominator]; ipra_ring))
    (original_joint_to_fixed_degree u z R B N L h hL)
  have last := distance_radius_mono _ _ (unit u+unit q) (unit u*unit q) ((unit u+unit q)*(V*unit p)) Z
    (positive_product _ _ (unit_positive u) (unit_positive q)) zp
    (le_of_eq_add (d := zero) (by dsimp only [Z,rateDenominator]; ipra_ring))
    (GaussianGammaFixedDegreeHorizon.observation_regularity u q z R B N L h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [rateNumerator,rateDenominator,unit]; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ zp (distance_triangle_same _ _ _ _ _ _ zp first middle) last)

theorem earlier_auxiliary_slack (z A B C s t : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hp : Γ ⊢[PRAAx] le (unit s) (unit t)) (h : Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack z A B C t) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack z A B C s := by
  have cross := add_le_add₂ (le_refl (A*B*unit s*unit t))
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (C*B*B)) hp)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ hB (unit_positive t)) (positive_product _ _ hB (unit_positive s))
    (le_congr (by unfold unit; ipra_ring) (by unfold unit; ipra_ring) cross) h

theorem cofinal_slack (p q t z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (point p z R B N) (observation q z R B N L))
      (rateNumerator (R*R) (rateDen N L) p q) (rateDenominator (rateDen N L) p q) (two*two) t := by
  let u := t+L
  have hL : Γ ⊢[PRAAx] le L (GammaCanonicalNames.degree u R) :=
    le_trans (le_add_left L t) (le_trans (le_add_right _ _) (le_add_right _ _))
  have grow : Γ ⊢[PRAAx] le (unit t) (unit u) :=
    GaussianFactorBudget.power_monotone_length two t u (le_succ_self one) (le_add_right t L)
  exact earlier_auxiliary_slack _ _ _ _ t u (denominator_positive _ p q (rate_den_positive N L h.andE₂.andE₁))
    grow (auxiliary_slack p q u z R B N L h hL)

theorem original_C18_observation_error (p q z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (point p z R B N) (observation q z R B N L)
      (rateNumerator (R*R) (rateDen N L) p q) (rateDenominator (rateDen N L) p q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (two*two)
    (denominator_positive _ p q (rate_den_positive N L h.andE₂.andE₁))
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,GaussianGammaCanonicalTailName.subst_point,
    GaussianGammaFixedDegreeHorizon.subst_observation,GaussianNamedInverseRate.subst_rateNumerator,
    GaussianNamedInverseRate.subst_rateDenominator,subst_rateDen,PTm.subst_mul,Syn.shift,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    cofinal_slack (Syn.shift p) (Syn.shift q) (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) (Syn.shift L) hs

theorem actual_C18_observation_error (p q z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (point p z R B N) (GaussianGammaFixedDegreeHorizon.sample q z R B N L)
      (rateNumerator (R*R) (rateDen N L) p q) (rateDenominator (rateDen N L) p q) :=
  distance_congr (.eqRefl _) (GaussianGammaFixedDegreeHorizon.sample_at q z R B N L).eqSymm (.eqRefl _) (.eqRefl _)
    (original_C18_observation_error p q z R B N L h)

theorem original_C18_name_rate (z R B N L : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    independentRate GaussianGammaCanonicalTailName.pointF GaussianGammaFixedDegreeHorizon.nameF
      (GaussianGammaCanonicalTailName.data z R B N) (GaussianGammaFixedDegreeHorizon.data z R B N L)
      (R*R) (rateDen N L) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [independentRate,GaussianGammaCanonicalTailName.point,GaussianGammaFixedDegreeHorizon.sample,
    GaussianGammaCanonicalTailName.subst_data,GaussianGammaFixedDegreeHorizon.subst_data,PTm.subst_mul,subst_rateDen,Syn.shift] using
    actual_C18_observation_error (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift L)) hs

theorem original_cofinal_C18_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      independentRate GaussianGammaCanonicalTailName.pointF GaussianGammaFixedDegreeHorizon.nameF
        (GaussianGammaCanonicalTailName.data (var 0) (var 1) (var 2) (var 3))
        (GaussianGammaFixedDegreeHorizon.data (var 0) (var 1) (var 2) (var 3) (var 4))
        (var 1*var 1) (rateDen (var 3) (var 4))) := closeUniv 5 (.impI (original_C18_name_rate _ _ _ _ _ Prf.hyp0))
theorem original_cofinal_C18_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (point (var 0) (var 2) (var 3) (var 4) (var 5))
        (GaussianGammaFixedDegreeHorizon.sample (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (rateNumerator (var 3*var 3) (rateDen (var 5) (var 6)) (var 0) (var 1))
        (rateDenominator (rateDen (var 5) (var 6)) (var 0) (var 1))) :=
  closeUniv 7 (.impI (actual_C18_observation_error _ _ _ _ _ _ _ Prf.hyp0))

theorem original_K_two_R_cofinal_C18_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
      independentRate GaussianGammaCanonicalTailName.pointF GaussianGammaFixedDegreeHorizon.nameF
        (GaussianGammaCanonicalTailName.data (var 0) (var 1) (var 2) (two*var 1))
        (GaussianGammaFixedDegreeHorizon.data (var 0) (var 1) (var 2) (two*var 1) (var 3))
        (var 1*var 1) (rateDen (two*var 1) (var 3))) :=
  closeUniv 4 (.impI (original_C18_name_rate _ _ _ _ _ (GaussianGammaCanonicalExponent.tail_source _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaCofinalDegreeTail
