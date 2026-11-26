import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitTimeRate

/-!
# Uniform compact variation of the actual nested unit logarithm

The original independently encoded samplers and their different Fast(2b,p)
queries remain unchanged. A true E-Lipschitz time rate and the proved
all-sample [1/E,E] guards give the diagonal E^2 rate plus fixed dyadic
slack. Source-derived regularity and the finite integer gap remove only
that auxiliary slack, preserving both requested observation allowances.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitLogarithmicRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitTimeRate (input)
open GaussianEulerUnitLogarithmicMargin (timeF timeData numerator denominator actual_time_fraction)
open GaussianEulerUnitLogarithmicComposition (nameF data sample query)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def lipschitz (E : PTm n) : PTm n := E*E
def cost (E : PTm n) : PTm n := two*E+two
@[simp] theorem subst_lipschitz {m : ℕ} (σ : Fin n → PTm m) (E : PTm n) :
    Syn.subst σ (lipschitz E) = lipschitz (Syn.subst σ E) := by simp [lipschitz]
@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (E : PTm n) :
    Syn.subst σ (cost E) = cost (Syn.subst σ E) := by simp [cost]

theorem diagonal (p a b c d E X Y : PTm n) (h : Γ ⊢[PRAAx] input a b c d E X Y) : Γ ⊢[PRAAx]
    distanceBounded (sample p a b) (sample p c d) ((lipschitz E*X)*unit p+cost E*Y) (Y*unit p) := by
  let r := query p b
  let s := query p d
  let P := unit p
  let U := unit (succ p)
  let A := (E*X)*P+two*Y
  let D := Y*P
  have hp := unit_positive (Γ := Γ) p
  have hr := unit_positive (Γ := Γ) r
  have hs := unit_positive (Γ := Γ) s
  have hY := h.andE₂.andE₂.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hY hp
  have rp : Γ ⊢[PRAAx] le P (unit r) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have sp : Γ ⊢[PRAAx] le P (unit s) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have old := GaussianEulerUnitTimeRate.original_observations r s a b c d E X Y h
  have timeNear : Γ ⊢[PRAAx] distanceBounded (ap2 timeF r (timeData a b)) (ap2 timeF s (timeData c d)) A D :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive Y r s hY) hD
      (by dsimp only [rateNumerator,rateDenominator,A,D,P]
          ipra_le (𝔞(Y)*𝔞(Y)*𝔞(unit s))*sl rp+(𝔞(Y)*𝔞(Y)*𝔞(unit r))*sl sp) old
  have left := GaussianEulerUnitCompactTimeBounds.evaluated_time_domain r a b E h.andE₁
  have right := GaussianEulerUnitCompactTimeBounds.evaluated_time_domain s c d E h.andE₂.andE₁
  have fractions := distance_congr (actual_time_fraction r a b (le_of_lt h.andE₁.andE₁.andE₂))
    (actual_time_fraction s c d (le_of_lt h.andE₂.andE₁.andE₁.andE₂)) (.eqRefl _) (.eqRefl _) timeNear
  have logRate := GaussianCompactLogarithmBounds.original_log_rate (numerator r a b) (denominator r a b)
    (numerator s c d) (denominator s c d) E A D left.andE₁ right.andE₁ hD left.andE₂.andE₁ right.andE₂.andE₁ fractions
  have raw := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (succ p) (succ p) logRate
  have later : Γ ⊢[PRAAx] le P U := GaussianExponentialReference.unit_monotone (le_succ_self p)
  have widened := distance_radius_mono _ _ _ _ ((lipschitz E*X)*P+cost E*Y) D
    (GaussianNamedInverseRate.denominator_positive D (succ p) (succ p) hD) hD
    (by dsimp only [rateNumerator,rateDenominator,D,A,U,P,lipschitz,cost]
        ipra_le (2*𝔞(Y)*𝔞(Y)*𝔞(unit p)*𝔞(unit (succ p)))*sl later) raw
  exact distance_congr (GaussianEulerUnitLogarithmicComposition.sample_at p a b).eqSymm
    (GaussianEulerUnitLogarithmicComposition.sample_at p c d).eqSymm (.eqRefl _) (.eqRefl _) widened

theorem diagonal_envelope (a b c d E X Y : PTm n) (h : Γ ⊢[PRAAx] input a b c d E X Y) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope nameF nameF (data a b) (data c d) (lipschitz E*X) Y (cost E) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift E) (Syn.shift X) (Syn.shift Y) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,GaussianEulerUnitLogarithmicComposition.subst_data,subst_lipschitz,
    subst_cost,PTm.subst_mul,Syn.shift,sample] using
    diagonal (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) (Syn.shift E) (Syn.shift X) (Syn.shift Y) hs

theorem original_rate (a b c d E X Y : PTm n) (h : Γ ⊢[PRAAx] input a b c d E X Y) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data a b) (data c d) (lipschitz E*X) Y :=
  GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ _ h.andE₂.andE₂.andE₁
    (GaussianEulerUnitLogarithmicComposition.name_regular a b h.andE₁.andE₁)
    (GaussianEulerUnitLogarithmicComposition.name_regular c d h.andE₂.andE₁.andE₁) (diagonal_envelope a b c d E X Y h)

theorem original_observations (p q a b c d E X Y : PTm n) (h : Γ ⊢[PRAAx] input a b c d E X Y) : Γ ⊢[PRAAx]
    distanceBounded (sample p a b) (sample q c d) (rateNumerator (lipschitz E*X) Y p q) (rateDenominator Y p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_rate a b c d E X Y h)

theorem actual_unit_compact_nested_logarithm_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      independentRate nameF nameF (data (var 0) (var 1)) (data (var 2) (var 3)) (lipschitz (var 4)*var 5) (var 6)) :=
  closeUniv 7 (.impI (original_rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitLogarithmicRate
