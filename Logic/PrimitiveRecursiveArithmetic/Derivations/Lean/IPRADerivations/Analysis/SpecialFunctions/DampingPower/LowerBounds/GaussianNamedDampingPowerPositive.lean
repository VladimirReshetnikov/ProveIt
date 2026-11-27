import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerRealSamples

/-!
# Sufficiently late positive observations of the original named chart

The compact lower envelope pays for the original power observation
error. The actual damping sample is positive by its source guard, so
the two literal factors in the chart multiply to a nonnegative real
rational code at every sufficiently late requested index.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerPositive

open_ipra
open GaussianNamedDampingPowerChart (source nameF data powerF powerData exponentRadius)
open GaussianNamedDampingPowerRealSamples (powerDenominator power_real original_power_lower)
open GaussianPositiveRealArithmetic (positive positive_congr sign)
open GaussianSignedNameExponentialOrder (real_sample_at)
open GaussianCoefficientNameBounds (unit)
open GaussianNameArithmetic (multiplyModulus)
open GaussianRationalHorner (qmul qmul_canonical)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_lower nonnegative_of_representation)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem power_denominator_positive (R E T : PTm n) : Γ ⊢[PRAAx] le one (powerDenominator R E T) :=
  GaussianFactorBudget.power_positive (num 3) (exponentRadius R E T) (le_of_eq_add (d := two) (by ipra_ring))

theorem parameter_positive_at (F : PR 2) (p x E T : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F x E T) : Γ ⊢[PRAAx] positive (ap2 F p x) := by
  have d := GaussianNamedPositiveLogarithm.decoded_domain F p x E T hs
  exact positive_congr (GaussianNamedPositiveLogarithm.decoded_value F p x E T hs)
    (GaussianEulerPositivePowerChartOrder.fraction_positive _ _ d.andE₁.andE₂)

theorem power_positive_at (G : PR 2) (p y R₀ R E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G y R₀ R)
    (hE : Γ ⊢[PRAAx] le one E) (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E T)
    (hp : Γ ⊢[PRAAx] le (two*powerDenominator R E T) (unit p)) : Γ ⊢[PRAAx] positive (ap2 (powerF G) p (powerData G y a b)) := by
  let M := powerDenominator R E T
  let D := two*M
  let v := fstT (ap2 (powerF G) p (powerData G y a b))
  have Mpos := power_denominator_positive (Γ := Γ) R E T
  have d := positive_product two M (le_succ_self one) Mpos
  have low := RationalCompactObservationTightening.lower_guard v M D (unit p) Mpos (le_refl D) hp
    (original_power_lower G p y R₀ R E T a b hs hE ht)
  have fsign : Γ ⊢[PRAAx] sign (fraction one D) := nonnegative_of_representation _ _ _ d
    (RationalIntegerNormalization.normalize_preserves_value _ _ d)
  exact .andI (real_sample_at _ _ _ (power_real G y R₀ R a b hs)).andE₂
    (nonnegative_of_lower _ _ fsign (RationalValueBounds.order_of_upper_zero (le_refl one) low))

theorem original_positive_at (F G : PR 2) (p x y C₀ C R₀ R E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source F G x y C₀ C R₀ R E T a b)
    (hp : Γ ⊢[PRAAx] le (two*powerDenominator R E T) (unit p)) : Γ ⊢[PRAAx] positive (ap2 (nameF F G) p (data F G x y a b)) := by
  let PF := powerF G
  let v := powerData G y a b
  let k := GaussianFastValueCut.exponent (multiplyModulus F PF x v) p
  have later : Γ ⊢[PRAAx] le p k := le_add_right p _
  have hPower := power_positive_at G k y R₀ R E T a b hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂
    (le_trans hp (GaussianCompactRiemannName.dyadic_monotone p k later))
  have hC := parameter_positive_at F k x C₀ C hs.andE₁
  have read := (GaussianNameArithmetic.multiply_at (Γ := Γ) F PF x v p).eqTrans
    (GaussianExponentialReference.recode_fixed (qmul (ap2 F k x) (ap2 PF k v)) (qmul_canonical _ _))
  exact positive_congr read.eqSymm (GaussianPositiveRealArithmetic.positive_multiply _ _ hC hPower)

theorem actual_named_damping_chart_late_samples_positive_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      (source F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
        le (two*powerDenominator (var 6) (var 7) (var 8)) (unit (var 0)) ⟶
        positive (ap2 (nameF F G) (var 0) (data F G (var 1) (var 2) (var 9) (var 10)))) :=
  closeUniv 11 (.impI (.impI (original_positive_at F G _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerPositive
