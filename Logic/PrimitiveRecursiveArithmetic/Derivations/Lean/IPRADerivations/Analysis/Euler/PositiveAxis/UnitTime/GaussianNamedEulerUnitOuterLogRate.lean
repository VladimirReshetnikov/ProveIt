import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianNamedEulerUnitTime

/-!
# The original outer log at a frozen unit sample versus a rational time

If the designated named unit time equals a compact positive rational,
the original nested log at any frozen sample of that input approaches
the original log of the rational time. The leading radius is exactly
E squared times the input query error. The outer log retains its own
original clock and both independently requested output allowances.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitOuterLogRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedEulerUnitTime (encodedTime)
open GaussianUnitIntervalInputDecoding (numerator denominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl)
open GaussianGammaCanonicalExponent (constantF constant_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (f : PR 2) (x a b E : PTm n) : Fm PTm n := GaussianNamedEulerUnitTime.source f x E ⋏
  (GaussianCompactLogarithmBounds.domain a b E E ⋏ crossEquivalent (GaussianNamedEulerUnitTime.nameF f) constantF
    (GaussianNamedEulerUnitTime.data x E) (fraction a b))
def frozenData (f : PR 2) (k x : PTm n) : PTm n :=
  GaussianEulerUnitLogarithmicComposition.data (numerator (ap2 f k x)) (denominator (ap2 f k x))
def cost (E : PTm n) : PTm n := two*E+two
abbrev logarithmF : PR 2 := GaussianEulerUnitLogarithmicComposition.nameF

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x a b E : PTm n) :
    (source f x a b E).subst σ = source f (Syn.subst σ x) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ E) := by simp [source]
@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x : PTm n) :
    Syn.subst σ (frozenData f k x) = frozenData f (Syn.subst σ k) (Syn.subst σ x) := by simp [frozenData]
@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (E : PTm n) :
    Syn.subst σ (cost E) = cost (Syn.subst σ E) := by simp [cost]

private theorem frozen_time_observations (f : PR 2) (r k x a b E : PTm n) (h : Γ ⊢[PRAAx] source f x a b E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 GaussianEulerUnitLogarithmicMargin.timeF r (encodedTime f k x))
      (fraction a b) (E*unit r+two*unit k) (unit k*unit r) := by
  have core := GaussianNamedEulerUnitTime.original_frozen_rate f k x E h.andE₁
  have regular := GaussianEulerUnitLogarithmicMargin.time_regular _ _ (GaussianNamedEulerUnitTime.encoded_source f k x E h.andE₁).andE₁
  have rate := GaussianNamedRateTransport.transport _ _ constantF _ _ _ (fraction a b) (encodedTime f k x) E (unit k)
    (unit_positive k) core (cross_symm _ _ _ _ h.andE₂.andE₂) (cross_refl _ _ regular)
  exact distance_congr (.eqRefl _) (constant_at r (fraction a b)) (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive k) (unit_positive r))
      (GaussianNamedInverseRate.diagonal_rate _ _ _ _ E (unit k) r (unit_positive k) rate))

theorem original_diagonal (f : PR 2) (p k x a b E : PTm n) (h : Γ ⊢[PRAAx] source f x a b E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 logarithmF p (frozenData f k x)) (ap2 logF p (GaussianPositiveRationalLogarithm.data a b))
      ((E*E)*unit p+cost E*unit k) (unit k*unit p) := by
  let c := numerator (ap2 f k x)
  let d := denominator (ap2 f k x)
  let r := GaussianEulerUnitLogarithmicComposition.query p d
  let P := unit p
  let Q := unit k
  let A := E*P+two*Q
  let D := Q*P
  have hc : Γ ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source c d E :=
    GaussianNamedEulerUnitTime.encoded_source f k x E h.andE₁
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive k) (unit_positive p)
  have late : Γ ⊢[PRAAx] le P (unit r) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have close := distance_radius_mono _ _ _ _ A D (positive_product _ _ (unit_positive k) (unit_positive r)) hd
    (by dsimp only [A,D,P,Q]; ipra_le (2*𝔞(unit k)^2)*sl late) (frozen_time_observations f r k x a b E h)
  have chart := GaussianEulerUnitCompactTimeBounds.evaluated_time_domain r c d E hc
  have toFraction := GaussianEulerUnitLogarithmicMargin.actual_time_fraction r c d (le_of_lt hc.andE₁.andE₂)
  have rate := GaussianCompactLogarithmBounds.original_log_rate _ _ a b E A D chart.andE₁ h.andE₂.andE₁.andE₁
    hd chart.andE₂.andE₁ h.andE₂.andE₁.andE₂.andE₁
    (distance_congr toFraction (.eqRefl _) (.eqRefl _) (.eqRefl _) close)
  have raw := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (succ p) p rate
  have weaker := distance_radius_mono _ _ _ _ ((E*E)*P+cost E*Q) D
    (GaussianNamedInverseRate.denominator_positive D (succ p) p hd) hd
    (by
      have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_succ_self p)
      dsimp only [rateNumerator,rateDenominator,A,D,P,Q,cost]
      ipra_le (𝔞(unit k)^2*𝔞(unit p)^2)*sl grow) raw
  exact distance_congr (GaussianEulerUnitLogarithmicComposition.sample_at p c d).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) weaker

theorem original_rate (f : PR 2) (k x a b E : PTm n) (h : Γ ⊢[PRAAx] source f x a b E) : Γ ⊢[PRAAx]
    independentRate logarithmF logF (frozenData f k x) (GaussianPositiveRationalLogarithm.data a b) (E*E) (unit k) := by
  have hc := GaussianNamedEulerUnitTime.encoded_source f k x E h.andE₁
  refine GaussianNamedLipschitzRate.independent_rate logarithmF logF (frozenData f k x)
    (GaussianPositiveRationalLogarithm.data a b) (E*E) (unit k) (cost E) (unit_positive k)
    (GaussianEulerUnitLogarithmicComposition.name_regular _ _ hc.andE₁)
    (GaussianPositiveRationalLogarithm.name_regular a b h.andE₂.andE₁.andE₁) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift a) (Syn.shift b) (Syn.shift E) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,subst_frozenData,GaussianPositiveRationalLogarithm.subst_data,
    subst_cost,GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,Syn.shift] using
    original_diagonal f (var 0) (Syn.shift k) (Syn.shift x) (Syn.shift a) (Syn.shift b) (Syn.shift E) hs

theorem actual_frozen_unit_outer_log_to_positive_log_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source f (var 1) (var 2) (var 3) (var 4) ⟶ independentRate logarithmF logF (frozenData f (var 0) (var 1))
      (GaussianPositiveRationalLogarithm.data (var 2) (var 3)) (var 4*var 4) (unit (var 0))) :=
  closeUniv 5 (.impI (original_rate f _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitOuterLogRate
