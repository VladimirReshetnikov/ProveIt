import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.Named.GaussianNamedEulerUnitKernel
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitTimeRate

/-!
# Positive logarithmic time on regular unit-interval names

The time sampler reads the original harmonic time at a fraction decoded
from an actual observation. The input clock pays for logarithm variation
on the certified compact interval, and the independent harmonic clock
pays for truncation. The original harmonic observations also give
all-sample positivity and upper bounds for the resulting time name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitTime

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianEulerUnitLogarithmicMargin (timeF timeData)
open GaussianUnitIntervalInputDecoding (numerator denominator fraction_recode)
open GaussianPositiveRationalLogarithm (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (f : PR 2) (x E : PTm n) : Fm PTm n :=
  pointCN f x ⋏ GaussianNamedEulerUnitKernel.admissibleSamples f x E
def clock (p E : PTm n) : PTm n := GaussianFastValueCut.exponent E (succ p)
def encodedTime (f : PR 2) (k x : PTm n) : PTm n :=
  timeData (numerator (ap2 f k x)) (denominator (ap2 f k x))
def observation (f : PR 2) (p x E : PTm n) : PTm n :=
  ap2 timeF (succ p) (encodedTime f (clock p E) x)
def data (x E : PTm n) : PTm n := pairT x E
def nameF (f : PR 2) : PR 2 := PTm.toPR
  (observation f (var 0) (fstT (var 1)) (sndT (var 1)))

ipra_subst clock
ipra_subst source
ipra_subst encodedTime
ipra_subst observation
ipra_subst data

theorem sample_at (f : PR 2) (p x E : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) p (data x E) ≐ observation f p x E := by
  simpa only [nameF, data, subst_observation, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    (toPR_pair_eq (Γ := Γ) (observation f (var 0) (var 1) (var 2)) p x E)

theorem source_at (f : PR 2) (r x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    GaussianUnitIntervalInputDecoding.source (ap2 f r x) E := by
  simpa [GaussianNamedEulerUnitKernel.admissibleSamples] using h.andE₂.allE r

theorem encoded_source (f : PR 2) (r x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    GaussianEulerUnitCompactTimeBounds.source (numerator (ap2 f r x)) (denominator (ap2 f r x)) E :=
  GaussianUnitIntervalInputDecoding.decoded_source _ _ (source_at f r x E h)

theorem sample_real (f : PR 2) (p x E : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (nameF f) p (data x E)) ⋏
    RationalGaussianEmbedding.axis (ap2 (nameF f) p (data x E)) := by
  have h := GaussianHarmonicLogarithmName.sample_real (Γ := Γ) (succ p)
    (denominator (ap2 f (clock p E) x)) (numerator (ap2 f (clock p E) x))
  have e := (sample_at (Γ := Γ) f p x E).eqSymm
  exact .andI (GaussianRationalHorner.canonical_congr e.eqSymm h.andE₁) (RationalGaussianEmbedding.axis_congr e h.andE₂)

theorem real_samples (f : PR 2) (x E : PTm n) : Γ ⊢[PRAAx]
    GaussianSignedNameExponentialOrder.realSamples (nameF f) (data x E) := by
  refine .allI ?_
  simpa only [GaussianSignedNameExponentialOrder.realSamples,subst_data,Syn.shift] using
    sample_real f (var 0) (Syn.shift x) (Syn.shift E)

theorem harmonic_time_bound (p a b E : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source a b E) :
    Γ ⊢[PRAAx] bounded (ap2 timeF p (timeData a b)) E one := by
  have domain := GaussianEulerUnitCompactTimeBounds.evaluated_time_domain p a b E h
  exact GaussianRationalReciprocal.bound_congr
    (GaussianEulerUnitLogarithmicMargin.actual_time_fraction p a b (le_of_lt h.andE₁.andE₂)).eqSymm
    (.eqRefl _) (.eqRefl _)
    (GaussianEulerExponentCompactBounds.fraction_bound _ _ E domain.andE₁.andE₂ domain.andE₂.andE₂)

theorem original_bound (f : PR 2) (p x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF f) p (data x E)) E one :=
  GaussianRationalReciprocal.bound_congr (sample_at f p x E).eqSymm (.eqRefl _) (.eqRefl _)
    (harmonic_time_bound (succ p) _ _ E (encoded_source f (clock p E) x E h))

private theorem rational_inputs (f g : PR 2) (r s x y E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    GaussianEulerUnitTimeRate.input (numerator (ap2 f r x)) (denominator (ap2 f r x))
      (numerator (ap2 g s y)) (denominator (ap2 g s y)) E (unit r+unit s) (unit r*unit s) := by
  have hD := positive_product _ _ (unit_positive (Γ := Γ) r) (unit_positive s)
  exact .andI (encoded_source f r x E hf) (.andI (encoded_source g s y E hg) (.andI hD
    (distance_congr (fraction_recode _ E (source_at f r x E hf)).eqSymm
      (fraction_recode _ E (source_at g s y E hg)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianFastValueCut.recode_distance_bound _ _ _ _ hD (cross_at f g x y r s he)))))

private theorem double_unit (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

private theorem time_clock_budget (p E : PTm n) : Γ ⊢[PRAAx] le (two*E*unit p) (unit (clock p E)) :=
  le_congr ((congrMul (.eqRefl E) (double_unit p)).eqTrans (by ipra_ring)) (.eqRefl _)
    (GaussianFastValueCut.query_budget E (succ p))

theorem original_observations (f g : PR 2) (p q x y E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x E)) (ap2 (nameF g) q (data y E))
      (unit p+unit q) (unit p*unit q) := by
  let r := clock p E
  let s := clock q E
  let A := unit r+unit s
  let D := unit r*unit s
  have raw := GaussianEulerUnitTimeRate.original_observations (succ p) (succ q) _ _ _ _ E A D
    (rational_inputs f g r s x y E hf hg he)
  have up := double_unit (Γ := Γ) p
  have uq := double_unit (Γ := Γ) q
  have eN : Γ ⊢[PRAAx] rateNumerator (E*A) D (succ p) (succ q) ≐
      (E*A)*(two*unit p)*(two*unit q)+D*(two*unit p+two*unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) uq) (congrMul (.eqRefl _) (congrAdd up uq))
  have eD : Γ ⊢[PRAAx] rateDenominator D (succ p) (succ q) ≐ D*(two*unit p)*(two*unit q) :=
    congrMul (congrMul (.eqRefl _) up) uq
  have adjusted := distance_congr (sample_at f p x E).eqSymm (sample_at g q y E).eqSymm eN eD raw
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (unit_positive r) (unit_positive s))
      (positive_product _ _ (zero_lt_succ one) (unit_positive p)))
      (positive_product _ _ (zero_lt_succ one) (unit_positive q)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (by
      dsimp only [A,D]
      ipra_le (2*𝔞(unit p)*𝔞(unit q)*𝔞(unit s)*𝔞(unit q))*sl (time_clock_budget p E)+
        (2*𝔞(unit p)*𝔞(unit q)*𝔞(unit r)*𝔞(unit p))*sl (time_clock_budget q E)) adjusted

theorem proper (f g : PR 2) (x y E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E) (hg : Γ ⊢[PRAAx] source g y E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) (nameF g) (data x E) (data y E) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hsf : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh] using hf.shift.shift
  have hsg : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source g (sh y) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh] using hg.shift.shift
  have hse : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) :=
    by simpa [Fm.shift,Syn.shift,sh] using he.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh] using
    original_observations f g (var 1) (var 0) (sh x) (sh y) (sh E) hsf hsg hse

theorem name_regular (f : PR 2) (x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    pointCN (nameF f) (data x E) := by
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,crossEquivalent] using
    proper f f x x E h h (GaussianNameEquivalence.cross_refl f x h.andE₁)

theorem original_frozen_observations (f : PR 2) (p q k x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x E)) (ap2 timeF q (encodedTime f k x))
      (rateNumerator E (unit k) p q) (rateDenominator (unit k) p q) := by
  let r := clock p E
  let A := unit r+unit k
  let D := unit r*unit k
  have raw := GaussianEulerUnitTimeRate.original_observations (succ p) q _ _ _ _ E A D
    (rational_inputs f f r k x x E h h (GaussianNameEquivalence.cross_refl f x h.andE₁))
  have up := double_unit (Γ := Γ) p
  have eN : Γ ⊢[PRAAx] rateNumerator (E*A) D (succ p) q ≐
      (E*A)*(two*unit p)*unit q+D*(two*unit p+unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) (.eqRefl _)) (congrMul (.eqRefl _) (congrAdd up (.eqRefl _)))
  have eD : Γ ⊢[PRAAx] rateDenominator D (succ p) q ≐ D*(two*unit p)*unit q :=
    congrMul (congrMul (.eqRefl _) up) (.eqRefl _)
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (unit_positive r) (unit_positive k))
      (positive_product _ _ (zero_lt_succ one) (unit_positive p))) (unit_positive q))
    (GaussianNamedInverseRate.denominator_positive _ p q (unit_positive k))
    (by dsimp only [A,D,rateNumerator,rateDenominator]
        ipra_le (𝔞(unit k)^2*𝔞(unit p)*𝔞(unit q)^2)*sl (time_clock_budget p E))
    (distance_congr (sample_at f p x E).eqSymm (.eqRefl _) eN eD raw)

theorem original_frozen_rate (f : PR 2) (k x E : PTm n) (h : Γ ⊢[PRAAx] source f x E) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate (nameF f) timeF (data x E) (encodedTime f k x) E (unit k) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [GaussianNamedInverseRate.independentRate,subst_data,subst_encodedTime,
    GaussianCoefficientNameBounds.subst_unit,Syn.shift,sh] using
    original_frozen_observations f (var 1) (var 0) (sh k) (sh x) (sh E) hs

theorem actual_named_unit_time_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source f (var 0) (var 1) ⟶ pointCN (nameF f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular f _ _ Prf.hyp0))

theorem actual_named_unit_time_proper_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 0) (var 2) ⟶ source g (var 1) (var 2) ⟶ crossEquivalent f g (var 0) (var 1) ⟶
      crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (proper f g _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

theorem actual_named_unit_time_frozen_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 1) (var 2) ⟶ GaussianNamedInverseRate.independentRate
      (nameF f) timeF (data (var 1) (var 2)) (encodedTime f (var 0) (var 1)) (var 2) (unit (var 0))) :=
  closeUniv 3 (.impI (original_frozen_rate f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitTime
