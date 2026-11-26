import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerIntegrand
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartLower

/-!
# Exact real observations of the named damping chart and decay

Reality is verified for the literal multiplication, logarithm, and
exponential programs. A compact lower envelope for the positive power
comes from the checked real exponential lower bound at a common radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerRealSamples

open_ipra
open GaussianNamedDampingPowerChart (source nameF data exponentF exponentData exponentRadius powerF powerData)
open GaussianNamedPositiveLogarithm (decoded_domain decoded_value)
open GaussianPositiveRationalLogarithm (logF)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianEulerDampedNamedIntegrand (decayF decayData)
open GaussianRationalHorner (canonical canonical_congr qmul qmul_canonical qzero)
open RationalGaussianEmbedding (axis axis_congr axis_multiply axis_zero axis_add axis_negative)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianRationalMetric (qsub qsub_canonical)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open RationalValueBounds (upper upper_of_radius upper_triangle upper_mono)
open GaussianNamedRealOrderTransport (remove_upper_slack upperSlack)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def powerDenominator (R E T : PTm n) : PTm n := pw (num 3) (exponentRadius R E T)

theorem parameter_real_at (F : PR 2) (p x E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F x E T) :
    Γ ⊢[PRAAx] canonical (ap2 F p x) ⋏ axis (ap2 F p x) := by
  have d := decoded_domain F p x E T h
  have exactSample := decoded_value F p x E T h
  exact .andI (GaussianNamedPositiveLogarithm.admissible_at F p x E T h).andE₁
    (axis_congr exactSample
      (GaussianEulerPositivePowerChartOrder.fraction_positive _ _ d.andE₁.andE₂).andE₁)

private theorem multiplication_real_at (F G : PR 2) (p x y : PTm n)
    (hF : Γ ⊢[PRAAx] realSamples F x) (hG : Γ ⊢[PRAAx] realSamples G y) :
    Γ ⊢[PRAAx] canonical (ap2 (multiplyF F G) p (multiplyData F G x y)) ⋏ axis (ap2 (multiplyF F G) p (multiplyData F G x y)) := by
  let k := GaussianFastValueCut.exponent (multiplyModulus F G x y) p
  have read := (GaussianNameArithmetic.multiply_at (Γ := Γ) F G x y p).eqTrans
    (GaussianExponentialReference.recode_fixed (qmul (ap2 F k x) (ap2 G k y)) (qmul_canonical _ _))
  exact .andI (canonical_congr read (qmul_canonical _ _))
    (axis_congr read.eqSymm (axis_multiply _ _ (real_sample_at F x k hF).andE₂ (real_sample_at G y k hG).andE₂))

private theorem multiplication_real (F G : PR 2) (x y : PTm n)
    (hF : Γ ⊢[PRAAx] realSamples F x) (hG : Γ ⊢[PRAAx] realSamples G y) :
    Γ ⊢[PRAAx] realSamples (multiplyF F G) (multiplyData F G x y) := by
  have fs : Γ.map Fm.shift ⊢[PRAAx] realSamples F (Syn.shift x) := by simpa only [Fm.shift,Syn.shift,GaussianSignedNameExponentialOrder.subst_realSamples] using hF.shift
  have gs : Γ.map Fm.shift ⊢[PRAAx] realSamples G (Syn.shift y) := by simpa only [Fm.shift,Syn.shift,GaussianSignedNameExponentialOrder.subst_realSamples] using hG.shift
  exact .allI (by simpa only [realSamples,Syn.shift,GaussianNameArithmetic.subst_multiplyData] using
    multiplication_real_at F G (var 0) (Syn.shift x) (Syn.shift y) fs gs)

private theorem parameter_real (F : PR 2) (x E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F x E T) : Γ ⊢[PRAAx] realSamples F x := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F (Syn.shift x) (Syn.shift E) (Syn.shift T) :=
    by simpa only [Fm.shift,Syn.shift,GaussianNamedPositiveLogarithm.subst_source] using h.shift
  exact .allI (parameter_real_at F (var 0) (Syn.shift x) (Syn.shift E) (Syn.shift T) hs)

private theorem rational_log_real (a b : PTm n) : Γ ⊢[PRAAx]
    realSamples logF (GaussianPositiveRationalLogarithm.data a b) := by
  refine .allI ?_
  have h : Γ.map Fm.shift ⊢[PRAAx] canonical (GaussianPositiveRationalLogarithm.sample (var 0) (Syn.shift a) (Syn.shift b)) ⋏
      axis (GaussianPositiveRationalLogarithm.sample (var 0) (Syn.shift a) (Syn.shift b)) :=
    .andI (GaussianPositiveRationalLogarithm.sample_canonical _ _ _) (GaussianPositiveRationalLogarithm.sample_axis _ _ _)
  simpa only [realSamples,Syn.shift,GaussianPositiveRationalLogarithm.subst_data,GaussianPositiveRationalLogarithm.sample] using h

theorem exponent_real (G : PR 2) (y R₀ R a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G y R₀ R) : Γ ⊢[PRAAx] realSamples (exponentF G) (exponentData G y a b) :=
  multiplication_real G logF y _ (parameter_real G y R₀ R h) (rational_log_real a b)

theorem power_real (G : PR 2) (y R₀ R a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G y R₀ R) : Γ ⊢[PRAAx] realSamples (powerF G) (powerData G y a b) :=
  GaussianEulerVerticalRealSamples.original_exponential_real_samples (exponentF G) _ (exponentData G y a b)
    (exponent_real G y R₀ R a b h)

theorem chart_real (F G : PR 2) (x y C₀ C R₀ R a b : PTm n)
    (h₁ : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F x C₀ C)
    (h₂ : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G y R₀ R) : Γ ⊢[PRAAx] realSamples (nameF F G) (data F G x y a b) :=
  multiplication_real F (powerF G) x (powerData G y a b) (parameter_real F x C₀ C h₁) (power_real G y R₀ R a b h₂)

theorem negative_real (F : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] realSamples F x) :
    Γ ⊢[PRAAx] realSamples (negativeF F) (negativeData x) := by
  let X := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSamples F X := by simpa only [Fm.shift,Syn.shift,GaussianSignedNameExponentialOrder.subst_realSamples,X] using h.shift
  let q := ap2 F (GaussianFastValueCut.exponent (one+one) (var 0)) X
  let r := qsub qzero q
  have read : Γ.map Fm.shift ⊢[PRAAx] ap2 (negativeF F) (var 0) (negativeData X) ≐ r :=
    (GaussianNameRingLaws.negative_at F X (var 0)).eqTrans (GaussianExponentialReference.recode_fixed r (qsub_canonical _ _))
  have hr : Γ.map Fm.shift ⊢[PRAAx] axis r := axis_add _ _ axis_zero
    (axis_negative _ (real_sample_at F X _ hs).andE₂)
  refine .allI ?_
  simpa only [realSamples,Syn.shift,GaussianNameRingLaws.subst_negativeData,X] using
    Prf.andI (canonical_congr read (qsub_canonical _ _)) (axis_congr read.eqSymm hr)

theorem decay_real (F G : PR 2) (x y C₀ C R₀ R a b : PTm n)
    (h₁ : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F x C₀ C)
    (h₂ : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G y R₀ R) : Γ ⊢[PRAAx]
    realSamples (decayF (nameF F G)) (decayData (nameF F G) (data F G x y a b)) :=
  GaussianEulerVerticalRealSamples.original_exponential_real_samples _ _ _
    (negative_real _ _ (chart_real F G x y C₀ C R₀ R a b h₁ h₂))

theorem original_power_lower (G : PR 2) (p y R₀ R E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G y R₀ R)
    (hE : Γ ⊢[PRAAx] le one E) (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E T) :
    Γ ⊢[PRAAx] upper (GaussianEuclideanDistanceName.fraction one (powerDenominator R E T))
      (fstT (ap2 (powerF G) p (powerData G y a b))) one (unit p) := by
  let F := exponentF G
  let X := exponentData G y a b
  let K := exponentRadius R E T
  let M := GaussianNameBounds.U F X
  let c := GaussianEuclideanDistanceName.fraction (one : PTm n) (powerDenominator R E T)
  let v := fstT (ap2 (powerF G) p (powerData G y a b))
  let j := GaussianNamedRealOrderTransport.precision c v (unit p) two
  have hi := GaussianNamedDampingPowerChart.exponent_input G y R₀ R E T a b h hE ht
  have old := GaussianGammaFiniteApproximantName.exponential_input F X hi.andE₁
  have cross := GaussianExponentialRadiusIndependence.same_input_cross F K M X hi old
  have lower := GaussianRealExponentialCompactLower.original_observation_lower F j K X hi (exponent_real G y R₀ R a b h)
  have near := GaussianNameEquivalence.cross_at _ _ _ _ j p cross
  have scalar := upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _
    (positive_product _ _ (unit_positive j) (unit_positive p)) near)
  have joined : Γ ⊢[PRAAx] upper c v (one*(unit j*unit p)+(unit j+unit p)*unit j) (unit j*(unit j*unit p)) :=
    upper_triangle _ _ _ _ _ _ _ lower scalar
  have budget : Γ ⊢[PRAAx] upperSlack c v one (unit p) two j :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive j)
      (positive_product _ _ (unit_positive j) (unit_positive p))) joined (le_of_eq_add (d := zero) (by ipra_ring))
  exact remove_upper_slack _ _ _ _ two budget

theorem actual_named_damping_decay_samples_real_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (GaussianNamedPositiveLogarithm.source F (var 0) (var 2) (var 3) ⟶
        GaussianNamedPositiveLogarithm.source G (var 1) (var 4) (var 5) ⟶
        realSamples (decayF (nameF F G)) (decayData (nameF F G) (data F G (var 0) (var 1) (var 6) (var 7)))) :=
  closeUniv 8 (.impI (.impI (decay_real F G _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_named_damping_power_compact_lower_closed (G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (GaussianNamedPositiveLogarithm.source G (var 1) (var 2) (var 3) ⟶ le one (var 4) ⟶
        GaussianCompactLogarithmBounds.domain (var 6) (var 7) (var 4) (var 5) ⟶
        upper (GaussianEuclideanDistanceName.fraction one (powerDenominator (var 3) (var 4) (var 5)))
          (fstT (ap2 (powerF G) (var 0) (powerData G (var 1) (var 6) (var 7)))) one (unit (var 0))) :=
  closeUniv 8 (.impI (.impI (.impI (original_power_lower G _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerRealSamples
