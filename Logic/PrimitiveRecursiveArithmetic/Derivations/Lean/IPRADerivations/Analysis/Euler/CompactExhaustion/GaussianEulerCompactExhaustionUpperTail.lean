import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerNamedUpperTail
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartImageCompactModulus

/-!
# Euler upper tails with arbitrary rational right endpoints

The panel starts at the original upper cutoff and ends at any rational
point above it. The ordinary compact name uses its actual mesh and
observation schedule. A cofinal finite estimate and regularity remove
the auxiliary sampling error, retaining the requested observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionUpperTail

open_ipra
open GaussianGammaIntegralCutoffs (height top)
open GaussianEulerPositivePowerChartImageCompactModulus (data nameF)
open GaussianEulerCompactModulus (lipschitz)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianCompactRiemannName (mesh precision quadrature)
open GaussianEulerUpperTailNameBudget (errorCost finiteNumerator finiteDenominator)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded qsub)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B k A C E G T : PTm n) : Fm PTm n :=
  GaussianGammaEulerCompactQuadrature.source z R B ⋏
    (le one E ⋏ (le one G ⋏ le (top k A R*E+C) (T*E)))

def point (p z R B k A C E G T : PTm n) : PTm n :=
  ap2 nameF p (data z R B (top k A R*E) C E G T)

def cofinalNumerator (s k A C R : PTm n) : PTm n :=
  two*majorant R*unit s+errorCost R C*unit (height k A R)

def cofinalDenominator (s k A R : PTm n) : PTm n :=
  unit (height k A R)*unit s

ipra_subst source [top, height, GaussianGammaIntegralCutoffs.tailCoefficient]

ipra_subst point [top, height, GaussianGammaIntegralCutoffs.tailCoefficient]

theorem panel_source (z R B k A C E G T : PTm n) (h : Γ ⊢[PRAAx] source z R B k A C E G T) :
    Γ ⊢[PRAAx] GaussianEulerPositivePowerChartImageCompactModulus.source z R B (top k A R*E) C E G T := by
  have ht := GaussianGammaIntegralCutoffs.top_positive (Γ := Γ) k A R
  have hE := h.andE₂.andE₁
  have hG := h.andE₂.andE₂.andE₁
  have low : Γ ⊢[PRAAx] le E (G*(top k A R*E)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right E (AnalyticNumberTheory.PhiLower.le_mul_mono hG ht))
  exact .andI (.andI h.andE₁.andE₁ (.andI hG h.andE₁.andE₂))
    (.andI (.andI (positive_product _ _ ht hE) hE) (.andI low h.andE₂.andE₂.andE₂))

theorem point_at (p z R B k A C E G T : PTm n) : Γ ⊢[PRAAx]
    point p z R B k A C E G T ≐ quadrature evaluatorF (precision p T) (mesh p (lipschitz R G T) T)
      (top k A R*E) C E (fixedData z B) :=
  GaussianCompactRiemannName.name_at evaluatorF p _ _ _ _ _ _

theorem point_regular (z R B k A C E G T : PTm n) (h : Γ ⊢[PRAAx] source z R B k A C E G T) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF (data z R B (top k A R*E) C E G T) :=
  GaussianEulerPositivePowerChartImageCompactModulus.name_regular _ _ _ _ _ _ _ _ (panel_source z R B k A C E G T h)

theorem point_canonical (p z R B k A C E G T : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (point p z R B k A C E G T) :=
  GaussianCompactRiemannName.name_canonical evaluatorF p _ _ _ _ _ _

theorem cofinal_denominator_positive (s k A R : PTm n) : Γ ⊢[PRAAx] le one (cofinalDenominator s k A R) :=
  positive_product _ _ (unit_positive _) (unit_positive s)

private theorem cofinal_bound_positive (s z R B k A C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B k A C E G T) (hC : Γ ⊢[PRAAx] le one C) : Γ ⊢[PRAAx]
    bounded (point s z R B k A C E G T) (cofinalNumerator s k A C R) (cofinalDenominator s k A R) := by
  let L := lipschitz R G T
  let P := precision s T
  let N := mesh s L T
  have hE := h.andE₂.andE₁
  have hN := GaussianCompactRiemannName.mesh_positive (Γ := Γ) s L T
  have hw : Γ ⊢[PRAAx] le C (E*T) :=
    le_congr (.eqRefl _) (mul_comm T E) (le_trans (le_add_left C (top k A R*E)) h.andE₂.andE₂.andE₂)
  have hs := GaussianEulerDecayCompactAntiderivative.mesh_covers_step s C E L T hw
    (GaussianEulerUpperTailNameBudget.lipschitz_positive R G T)
  have step : Γ ⊢[PRAAx] le C ((two*E)*N) :=
    le_trans hs (le_of_eq_add (d := E*N) (by ipra_ring))
  have raw := GaussianEulerCompactUpperTail.original_upper_cutoff_bound P s N k A C E z R B hN hC hE step h.andE₁
  have widened := bounded_radius_mono _ _ _ (cofinalNumerator s k A C R) (cofinalDenominator s k A R)
    (GaussianEulerUpperTailNameBudget.denominator_positive P s N (height k A R) E hE hN)
    (cofinal_denominator_positive s k A R)
    (GaussianEulerUpperTailNameBudget.finite_budget P s N (height k A R) C E R hE
      (GaussianEulerUpperTailNameBudget.mesh_unit_lower s L T)
      (GaussianEulerUpperTailNameBudget.precision_unit_lower s T)) raw
  exact bound_congr (point_at s z R B k A C E G T).eqSymm (.eqRefl _) (.eqRefl _) widened

theorem point_zero_of_width_zero (s z R B k A C E G T : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hC : Γ ⊢[PRAAx] C ≐ zero) :
    Γ ⊢[PRAAx] point s z R B k A C E G T ≐ qzero := by
  have same : Γ ⊢[PRAAx] point s z R B k A C E G T ≐ point s z R B k A zero E G T := by
    simpa using Prf.eqCongr1 (point (Syn.shift s) (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift k) (Syn.shift A) (var 0) (Syn.shift E) (Syn.shift G) (Syn.shift T)) hC
  exact same.eqTrans (GaussianCompactZeroWidth.observation_zero evaluatorF s (top k A R*E) E
    (lipschitz R G T) T (fixedData z B) hE)

theorem cofinal_bound (s z R B k A C E G T : PTm n) (h : Γ ⊢[PRAAx] source z R B k A C E G T) :
    Γ ⊢[PRAAx] bounded (point s z R B k A C E G T) (cofinalNumerator s k A C R) (cofinalDenominator s k A R) := by
  refine .orE (zero_or_succ C) ?_ ?_
  · exact bound_congr (point_zero_of_width_zero s z R B k A C E G T h.wk.andE₂.andE₁ Prf.hyp0).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianEulerNamedUpperTail.zero_bound _ _ (cofinal_denominator_positive s k A R))
  · have hc : (C ≐ succ (pred C))::Γ ⊢[PRAAx] le one C :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact cofinal_bound_positive s z R B k A C E G T h.wk hc

private theorem observation_slack (p s z R B k A C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B k A C E G T) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (point p z R B k A C E G T)
      (GaussianEulerNamedUpperTail.numerator p k A R) (GaussianEulerNamedUpperTail.denominator p k A R)
      (errorCost R C+one) s := by
  have u := unit_positive (Γ := Γ) p
  have v := unit_positive (Γ := Γ) s
  have dv := cofinal_denominator_positive (Γ := Γ) s k A R
  have dm := positive_product (Γ := Γ) _ _ u v
  have close := GaussianNameEquivalence.point_at nameF (data z R B (top k A R*E) C E G T) p s
    (point_regular z R B k A C E G T h)
  have sum := GaussianRationalReciprocal.bounded_sum (point s z R B k A C E G T)
    (qsub (point p z R B k A C E G T) (point s z R B k A C E G T))
    (cofinalNumerator s k A C R) (cofinalDenominator s k A R) (unit p+unit s) (unit p*unit s) dv dm
    (cofinal_bound s z R B k A C E G T h) close
  have exactPoint := GaussianRationalLinearProduct.add_sub_right (Γ := Γ)
    (point s z R B k A C E G T) (point p z R B k A C E G T) (point_canonical p z R B k A C E G T)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ dv dm)
    (positive_product _ _ (GaussianEulerNamedUpperTail.denominator_positive p k A R) v) _
    (bound_congr exactPoint (.eqRefl _) (.eqRefl _) sum)
  exact le_of_eq_add (d := zero) (by
    unfold cofinalNumerator cofinalDenominator GaussianEulerNamedUpperTail.numerator GaussianEulerNamedUpperTail.denominator unit
    ipra_ring)

theorem original_named_upper_tail (p z R B k A C E G T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B k A C E G T) : Γ ⊢[PRAAx]
    bounded (point p z R B k A C E G T)
      (GaussianEulerNamedUpperTail.numerator p k A R) (GaussianEulerNamedUpperTail.denominator p k A R) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (errorCost R C+one)
    (GaussianEulerNamedUpperTail.denominator_positive p k A R)
    (observation_slack p (GaussianRationalSlackRemoval.precision (point p z R B k A C E G T)
      (GaussianEulerNamedUpperTail.numerator p k A R) (GaussianEulerNamedUpperTail.denominator p k A R)
      (errorCost R C+one)) z R B k A C E G T h)

theorem actual_named_Euler_upper_tail_arbitrary_right_endpoint_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        bounded (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
          (GaussianEulerNamedUpperTail.numerator (var 0) (var 4) (var 5) (var 2))
          (GaussianEulerNamedUpperTail.denominator (var 0) (var 4) (var 5) (var 2))) :=
  closeUniv 10 (.impI (original_named_upper_tail _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionUpperTail
