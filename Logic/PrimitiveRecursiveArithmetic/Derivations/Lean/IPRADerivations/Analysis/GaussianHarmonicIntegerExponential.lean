import IPRADerivations.Analysis.GaussianBoundedIntegerExponential
import IPRADerivations.Analysis.GaussianHarmonicLogarithmName
import IPRADerivations.Analysis.GaussianNaturalScaleProductName
import IPRADerivations.Analysis.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.GaussianEulerExponentCompactBounds
import IPRADerivations.Analysis.RationalNonnegativePowers

/-!
# Numerical integer powers of the actual positive-time logarithm

Original compact time guards discharge the generic bounded integer
exponential source. Its value is the original normalized rational power
a^m/b^m. Actual name multiplication and exponential properness then bind
the same value to the unchanged original log program and its original
exponential after multiplication by the actual natural point m.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicIntegerExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianHarmonicLogarithmName (radius)
open GaussianRationalReciprocal (power)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_to_diagonal)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (a b E T : PTm n) : Fm PTm n := le one E ⋏ GaussianCompactLogarithmBounds.domain a b E T
def scaledExpF : PR 2 := GaussianBoundedIntegerExponentialStages.expF GaussianHarmonicLogarithmName.nameF
def scaledData (m a b E T : PTm n) : PTm n := GaussianBoundedIntegerExponentialStages.expData
  m m (radius E T) (GaussianHarmonicLogarithmName.data a b)
def scaledQuery (p m E T : PTm n) : PTm n := GaussianNamedNaturalScale.clock
  (GaussianRadiusExponentialName.inputPrecision (GaussianNamedNaturalScale.radius m (radius E T)) p) m
def scaledCutoff (p m E T : PTm n) : PTm n :=
  GaussianRadiusExponentialName.index (GaussianNamedNaturalScale.radius m (radius E T)) p
def originalExponentF : PR 2 := GaussianNaturalScaleProductName.productF logF
def originalExponentData (m a b : PTm n) : PTm n := GaussianNaturalScaleProductName.productData logF
  m (GaussianPositiveRationalLogarithm.data a b)
def originalExpF : PR 2 := GaussianRadiusExponentialName.nameF originalExponentF
def originalData (m a b : PTm n) : PTm n := GaussianGammaFiniteApproximantName.exponentialInputData originalExponentF (originalExponentData m a b)
def originalRadius (m a b : PTm n) : PTm n := GaussianNameBounds.U originalExponentF (originalExponentData m a b)
def originalQuery (p m a b : PTm n) : PTm n := GaussianNaturalScaleProductName.clock logF
  (GaussianRadiusExponentialName.inputPrecision (originalRadius m a b) p) m (GaussianPositiveRationalLogarithm.data a b)
def rationalPower (a b m : PTm n) : PTm n := RationalGaussianEmbedding.embed (RationalNonnegativePowers.power a b m)

@[simp] theorem subst_source {k : ℕ} (σ : Fin n → PTm k) (a b E T : PTm n) :
    (source a b E T).subst σ = source (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ E) (Syn.subst σ T) := by simp [source]
@[simp] theorem subst_scaledData {k : ℕ} (σ : Fin n → PTm k) (m a b E T : PTm n) :
    Syn.subst σ (scaledData m a b E T) = scaledData (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ E) (Syn.subst σ T) := by simp [scaledData]
@[simp] theorem subst_originalExponentData {k : ℕ} (σ : Fin n → PTm k) (m a b : PTm n) :
    Syn.subst σ (originalExponentData m a b) = originalExponentData (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ b) := by simp [originalExponentData]
@[simp] theorem subst_originalData {k : ℕ} (σ : Fin n → PTm k) (m a b : PTm n) :
    Syn.subst σ (originalData m a b) = originalData (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [originalData,GaussianGammaFiniteApproximantName.exponentialInputData]
@[simp] theorem subst_rationalPower {k : ℕ} (σ : Fin n → PTm k) (a b m : PTm n) :
    Syn.subst σ (rationalPower a b m) = rationalPower (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ m) := by simp [rationalPower]

theorem bounded_input (a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    GaussianBoundedIntegerExponentialStages.input GaussianHarmonicLogarithmName.nameF (radius E T)
      (GaussianHarmonicLogarithmName.data a b) (fraction a b) T :=
  .andI (GaussianHarmonicLogarithmName.common_input a b E T h.andE₁ h.andE₂)
    (.andI (GaussianHarmonicLogarithmName.original_exponential_fraction a b E T h.andE₁ h.andE₂)
      (GaussianEulerExponentCompactBounds.fraction_bound a b T h.andE₂.andE₁.andE₂ h.andE₂.andE₂.andE₂))

theorem scaled_sample_finite (p m a b E T : PTm n) : Γ ⊢[PRAAx]
    ap2 scaledExpF p (scaledData m a b E T) ≐ GaussianRationalPolynomialExponential.scalarSum
      (GaussianRationalNaturalScale.natScale m (GaussianHarmonicLogarithmName.sample (scaledQuery p m E T) a b))
      (scaledCutoff p m E T) :=
  (GaussianRadiusExponentialName.sample_at (GaussianNamedNaturalScale.nameF GaussianHarmonicLogarithmName.nameF)
    (GaussianNamedNaturalScale.radius m (radius E T)) p (GaussianNamedNaturalScale.data m m (GaussianHarmonicLogarithmName.data a b))).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
      (GaussianNamedNaturalScale.sample_at GaussianHarmonicLogarithmName.nameF
        (GaussianRadiusExponentialName.inputPrecision (GaussianNamedNaturalScale.radius m (radius E T)) p)
        m m (GaussianHarmonicLogarithmName.data a b)))

/-- This literal finite-sum binding keeps the original log-product query
inside the original exponential's actual computed input precision. -/
theorem original_sample_finite (p m a b : PTm n) : Γ ⊢[PRAAx]
    ap2 originalExpF p (originalData m a b) ≐ GaussianRationalPolynomialExponential.scalarSum
      (GaussianRationalNaturalScale.natScale m (GaussianPositiveRationalLogarithm.sample (originalQuery p m a b) a b))
      (GaussianRadiusExponentialName.index (originalRadius m a b) p) :=
  (GaussianRadiusExponentialName.sample_at originalExponentF (originalRadius m a b) p (originalExponentData m a b)).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
      (GaussianNaturalScaleProductName.product_at logF (GaussianRadiusExponentialName.inputPrecision (originalRadius m a b) p)
        m (GaussianPositiveRationalLogarithm.data a b)))

/-- The target is the original scalar power program, not a separately
postulated analytic value or a new polynomial power. -/
theorem actual_rational_power (a b m : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    power (fraction a b) m ≐ rationalPower a b m := by
  have first := (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl m)
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb))
  have hp := GaussianPolynomialPerturbation.power_positive b m hb
  have rep := RationalNonnegativePowers.power_represents (Γ := Γ) a b m hb
  have last := GaussianRationalHorner.canonical_unique _ _ _ (pw b m)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hp) (RationalGaussianEmbedding.embed_canonical _) hp
    (GaussianDominantPairAlgebra.radius_represents (pw a m) (pw b m) hp)
    (RationalGaussianEmbedding.embed_from_representation _ _ _ rep)
  exact first.eqTrans ((GaussianDominantPairAlgebra.radius_power a b m hb).eqTrans last)

theorem scaled_integer_power (m a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    crossEquivalent scaledExpF constantF (scaledData m a b E T) (rationalPower a b m) :=
  cross_trans _ _ _ _ _ _
    (GaussianBoundedIntegerExponential.integer_power_cross GaussianHarmonicLogarithmName.nameF m (radius E T)
      (GaussianHarmonicLogarithmName.data a b) (fraction a b) T (bounded_input a b E T h))
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (actual_rational_power a b m h.andE₂.andE₁.andE₂))

theorem original_exponent_regular (m a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN originalExponentF (originalExponentData m a b) :=
  GaussianNameArithmetic.multiply_fast constantF logF _ _ (constant_regular _)
    (GaussianPositiveRationalLogarithm.name_regular a b h.andE₂.andE₁)

theorem scaled_to_original_exponent (m a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNamedNaturalScale.nameF GaussianHarmonicLogarithmName.nameF) originalExponentF
      (GaussianNamedNaturalScale.data m m (GaussianHarmonicLogarithmName.data a b)) (originalExponentData m a b) := by
  let H := GaussianHarmonicLogarithmName.nameF
  let X := GaussianHarmonicLogarithmName.data a b
  let Y := GaussianPositiveRationalLogarithm.data a b
  let C := GaussianRationalNaturalScale.naturalPoint m
  have scaled := GaussianNaturalScaleProductName.scale_product_cross H m m (radius E T) X
    (GaussianHarmonicLogarithmName.common_input a b E T h.andE₁ h.andE₂) (le_refl _)
  have proper := GaussianNameArithmetic.multiply_equivalent constantF constantF H logF C C X Y
    (constant_regular C) (constant_regular C) (GaussianHarmonicLogarithmName.name_regular a b h.andE₂.andE₁)
    (GaussianPositiveRationalLogarithm.name_regular a b h.andE₂.andE₁) (GaussianNameEquivalence.diagonal_refl constantF C)
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a b h.andE₂.andE₁)))
  exact cross_trans _ _ _ _ _ _ scaled proper

/-- Actual original log multiplication and its original exponential data
have the exact original rational power for every internal m, including0. -/
theorem original_integer_exponential (m a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    crossEquivalent originalExpF constantF (originalData m a b) (rationalPower a b m) := by
  let H := GaussianHarmonicLogarithmName.nameF
  let X := GaussianHarmonicLogarithmName.data a b
  have inputH := GaussianBoundedIntegerExponentialStages.stage_input H m m (radius E T) X (fraction a b) T
    (bounded_input a b E T h) (le_refl _)
  have original := GaussianGammaFiniteApproximantName.exponential_input originalExponentF (originalExponentData m a b)
    (original_exponent_regular m a b E T h)
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper (GaussianNamedNaturalScale.nameF H) originalExponentF
    (GaussianNamedNaturalScale.radius m (radius E T)) (GaussianNameBounds.U originalExponentF (originalExponentData m a b))
    (GaussianNamedNaturalScale.data m m X) (originalExponentData m a b) inputH original (scaled_to_original_exponent m a b E T h)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ proper) (scaled_integer_power m a b E T h)

theorem rational_power_top_bound (m a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (rationalPower a b m) (pw T m) one :=
  GaussianRationalReciprocal.bound_congr (actual_rational_power a b m h.andE₂.andE₁.andE₂) (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_power_integer _ T m
      (GaussianEulerExponentCompactBounds.fraction_bound a b T h.andE₂.andE₁.andE₂ h.andE₂.andE₂.andE₂))

/-- The unchanged original exponential observations have the exact top
power bound, with only their requested ordinary observation error. -/
theorem original_integer_exponential_top_bound (p m a b E T : PTm n) (h : Γ ⊢[PRAAx] source a b E T) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (ap2 originalExpF p (originalData m a b))
      (pw T m*GaussianCoefficientNameBounds.unit p+one) (GaussianCoefficientNameBounds.unit p) := by
  let x := ap2 originalExpF p (originalData m a b)
  let c := rationalPower a b m
  let U := GaussianCoefficientNameBounds.unit p
  let A := pw T m*U+one
  let t := GaussianRationalSlackRemoval.precision x A U one
  have u := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) p
  have v := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) t
  have close := GaussianNameEquivalence.cross_at _ _ _ _ p t (original_integer_exponential m a b E T h)
  have distance := GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (GaussianGammaCanonicalExponent.constant_at t c)
    (.eqRefl _) (.eqRefl _) close
  have bound := GaussianRationalReciprocal.bounded_sum c (GaussianRationalMetric.qsub x c) (pw T m) one
    (U+GaussianCoefficientNameBounds.unit t) (U*GaussianCoefficientNameBounds.unit t) (le_refl one)
    (GaussianRationalHorner.positive_product _ _ u v) (rational_power_top_bound m a b E T h) distance
  have canonical := GaussianRadiusExponentialName.sample_canonical (Γ := Γ) originalExponentF (originalRadius m a b) p (originalExponentData m a b)
  apply GaussianRationalSlackRemoval.slack_removal_at x A U one u
  exact GaussianRationalReciprocal.bound_congr (GaussianRationalLinearProduct.add_sub_right c x canonical)
    (by dsimp only [A,t,GaussianCoefficientNameBounds.unit]; ipra_ring) (one_mul _) bound

theorem original_integer_time_exponential_rational_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent originalExpF constantF (originalData (var 0) (var 1) (var 2)) (rationalPower (var 1) (var 2) (var 0))) :=
  closeUniv 5 (.impI (original_integer_exponential _ _ _ _ _ Prf.hyp0))

theorem actual_original_integer_log_exponential_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 originalExpF (var 0) (originalData (var 1) (var 2) (var 3)) ≐ GaussianRationalPolynomialExponential.scalarSum
      (GaussianRationalNaturalScale.natScale (var 1) (GaussianPositiveRationalLogarithm.sample (originalQuery (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)))
      (GaussianRadiusExponentialName.index (originalRadius (var 1) (var 2) (var 3)) (var 0))) :=
  closeUniv 4 (original_sample_finite _ _ _ _)

theorem original_integer_time_exponential_top_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶
      GaussianRationalMetric.bounded (ap2 originalExpF (var 0) (originalData (var 1) (var 2) (var 3)))
        (pw (var 5) (var 1)*GaussianCoefficientNameBounds.unit (var 0)+one) (GaussianCoefficientNameBounds.unit (var 0))) :=
  closeUniv 6 (.impI (original_integer_exponential_top_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianHarmonicIntegerExponential
