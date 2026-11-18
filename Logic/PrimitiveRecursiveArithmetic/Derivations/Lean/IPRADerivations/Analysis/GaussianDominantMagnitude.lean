import IPRADerivations.Analysis.GaussianOffDominantSum
import IPRADerivations.Analysis.GaussianDescentClockArithmetic

/-!
# Exact lower and upper bounds for the computed dominant term

The actual failed coefficient at the balanced starting radius supplies a
strict lower bound. The computed plateau center lies below 2N, and its
actual winner dominates that same coefficient. Clearing only proved
positive denominators gives the original source constant
D = 2^N * 4^(2*N*N), without computing a square root or supplying a
positive maximum, lower bound or successful-search hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantMagnitude

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (input unit unit_positive coefficient)
open LeanProofs.IPRA.Analysis.GaussianDominantSyntax
  (four exponent score numerator denominator score_represents denominator_positive)
open LeanProofs.IPRA.Analysis.GaussianDescentClockArithmetic (descentD)
open LeanProofs.IPRA.Analysis.GaussianDominantPlateau (center winner)
open LeanProofs.IPRA.Analysis.GaussianOffDominantSum (selectedScore)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def restoreFactor (h i : PTm n) : PTm n := unit (four*h*i)
def squaredBudget (N : PTm n) : PTm n := descentD N*descentD N
def multiple (W q : PTm n) : PTm n := RationalArithmetic.multiply (fraction W one) q
def constantScore (C N : PTm n) : PTm n := GaussianRationalMetric.qnormSq (coefficient C N zero)
def lowerBound (C N : PTm n) : Fm PTm n := neg
  (RationalArgmin.rationalLE (multiple (squaredBudget N) (selectedScore C N)) (constantScore C N))
def upperBound (C N : PTm n) : Fm PTm n := RationalArgmin.rationalLE (selectedScore C N) (constantScore C N)

@[simp] theorem subst_restoreFactor {m : ℕ} (σ : Fin n → PTm m) (h i : PTm n) :
    Syn.subst σ (restoreFactor h i) = restoreFactor (Syn.subst σ h) (Syn.subst σ i) := by simp [restoreFactor]
@[simp] theorem subst_squaredBudget {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (squaredBudget N) = squaredBudget (Syn.subst σ N) := by simp [squaredBudget]
@[simp] theorem subst_multiple {m : ℕ} (σ : Fin n → PTm m) (W q : PTm n) :
    Syn.subst σ (multiple W q) = multiple (Syn.subst σ W) (Syn.subst σ q) := by simp [multiple]
@[simp] theorem subst_constantScore {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (constantScore C N) = constantScore (Syn.subst σ C) (Syn.subst σ N) := by simp [constantScore]
@[simp] theorem subst_lowerBound {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (lowerBound C N).subst σ = lowerBound (Syn.subst σ C) (Syn.subst σ N) := by simp [lowerBound]
@[simp] theorem subst_upperBound {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (upperBound C N).subst σ = upperBound (Syn.subst σ C) (Syn.subst σ N) := by simp [upperBound]

theorem denominator_factor (C N E h i : PTm n) : Γ ⊢[PRAAx]
    denominator C N E h i ≐ GaussianBalancedRadiusValues.scaledDenominator C N E i*restoreFactor h i := by
  have ex : Γ ⊢[PRAAx] two*exponent E h*i ≐ two*E*i+four*h*i := by unfold exponent four; ipra_ring
  exact (congrMul (.eqRefl _) ((congrAp2 powF ex (.eqRefl two)).eqTrans (pw_add two _ _))).eqTrans
    (by unfold GaussianBalancedRadiusValues.scaledDenominator restoreFactor unit; ipra_ring)

theorem multiple_represents (W q A B : PTm n)
    (hq : Γ ⊢[PRAAx] RationalArithmetic.represents q (ZT.ofNat A) B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (multiple W q) (ZT.ofNat (W*A)) B := by
  have raw := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (fraction_represents W one (le_refl one)) hq
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _) (h := raw)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

theorem descent_dyadic (N : PTm n) : Γ ⊢[PRAAx] descentD N ≐ unit (N+four*N*N) := by
  have rest := (GaussianBalancedRadiusArithmetic.unit_four_power (Γ := Γ) (two*N*N)).eqSymm
  exact (congrMul (.eqRefl (unit N)) rest).eqTrans
    ((pw_add two N (two*(two*N*N))).eqSymm.eqTrans
      (congrAp2 powF (by unfold four; ipra_ring) (.eqRefl two)))

theorem budget_dyadic (N : PTm n) : Γ ⊢[PRAAx]
    squaredBudget N ≐ unit (two*N+two*four*N*N) :=
  (congrMul (descent_dyadic N) (descent_dyadic N)).eqTrans
    ((GaussianBalancedRadiusArithmetic.unit_square (N+four*N*N)).eqTrans
      (congrAp2 powF (by ipra_ring) (.eqRefl two)))

theorem factor_budget (N h i : PTm n) (hh : Γ ⊢[PRAAx] le h (two*N)) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    le (pw four N*restoreFactor h i) (squaredBudget N) := by
  have ex : Γ ⊢[PRAAx] le (two*N+four*h*i) (two*N+two*four*N*N) :=
    add_le_add₂ (le_refl _) (le_congr (.eqRefl _) (by ipra_ring)
      (le_mul_mono (le_mul_mono (le_refl four) hh) hi))
  have joined : Γ ⊢[PRAAx] pw four N*restoreFactor h i ≐ unit (two*N+four*h*i) :=
    (congrMul (GaussianBalancedRadiusArithmetic.unit_four_power N).eqSymm (.eqRefl _)).eqTrans (pw_add two _ _).eqSymm
  exact le_congr joined.eqSymm (budget_dyadic N).eqSymm (GaussianBalancedRadiusArithmetic.unit_monotone _ _ ex)

/-- Opposite maximum/lower comparisons contradict the actual strict
balanced witness. Only the current denominator and scale factor cancel. -/
theorem strict_budget_contradiction (a b A B F P Q c d : PTm n)
    (hMax : Γ ⊢[PRAAx] le (B*a) (b*(A*F)))
    (hOpp : Γ ⊢[PRAAx] le (d*Q*b) (c*B))
    (hFactor : Γ ⊢[PRAAx] le (P*F) Q)
    (hFail : Γ ⊢[PRAAx] lt (c*A) (P*d*a))
    (hB : Γ ⊢[PRAAx] le one B) (hF : Γ ⊢[PRAAx] le one F) : Γ ⊢[PRAAx] Fm.bot := by
  have first := mul_le_mul_right (d*Q) hMax
  have second := mul_le_mul_right (A*F) hOpp
  have chain : Γ ⊢[PRAAx] le (B*(d*Q*a)) (c*B*(A*F)) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) first) second
  have cancelled : Γ ⊢[PRAAx] le (d*Q*a) (c*A*F) :=
    RationalValueBounds.positive_cancel hB (le_congr (.eqRefl _) (by ipra_ring) chain)
  have small := mul_le_mul_right (d*a) hFactor
  have again : Γ ⊢[PRAAx] le (F*(P*d*a)) (F*(c*A)) :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) small)
      (le_congr (.eqRefl _) (by ipra_ring) cancelled)
  exact le_lt_absurd Fm.bot (RationalValueBounds.positive_cancel hF again) hFail

theorem score_below_initial (C N E j h i : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (score C N E j h i) (GaussianBalancedRadiusValues.scaledNorm C N E j i) := by
  have natural := le_mul_mono (Γ := Γ) (le_refl (numerator C N j i*GaussianBalancedRadiusValues.scaledDenominator C N E i))
    (unit_positive (four*h*i))
  exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (denominator_positive C N E h i) (GaussianBalancedRadiusValues.scaled_denominator_positive C N E i)
    (score_represents C N E j h i) (GaussianBalancedRadiusValues.scaledNorm_represents C N E j i)
    (le_congr (by ipra_ring) (congrMul (.eqRefl _) (denominator_factor C N E h i)).eqSymm
      (le_congr (.eqRefl _) (by unfold numerator restoreFactor; ipra_ring) natural))

theorem dominant_lower (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] lowerBound C N := by
  refine .impI ?_
  let Δ := RationalArgmin.rationalLE (multiple (squaredBudget N) (selectedScore C N)) (constantScore C N)::Γ
  let E := GaussianBalancedRadiusHeight.E C N
  let j := GaussianBalancedRadiusSearch.radiusIndex C N
  let h := center C N
  let k := winner C N
  let w := GaussianBalancedRadiusSearch.witness C N
  have witness := GaussianBalancedRadiusSearch.witness_spec (Γ := Δ) C N hInput.wk
  have wi : Δ ⊢[PRAAx] le one w := Prf.andE₁ witness
  have wN : Δ ⊢[PRAAx] le w N := Prf.andE₁ (Prf.andE₂ witness)
  have failed := GaussianBalancedRadiusArithmetic.actual_balanced_witness C N E j w wN
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ witness)))
  have hFail : Δ ⊢[PRAAx] lt
      (GaussianBalancedRadiusSyntax.numerator C N zero*GaussianBalancedRadiusValues.scaledDenominator C N E w)
      (pw four N*GaussianBalancedRadiusSyntax.denominator C N zero*numerator C N j w) :=
    lt_congr (by unfold GaussianBalancedRadiusSyntax.cap GaussianBalancedRadiusValues.scaledDenominator; ipra_ring)
      (by unfold GaussianBalancedRadiusSyntax.score numerator GaussianBalancedRadiusValues.scaledNumerator four; ipra_ring) failed
  have max := GaussianDominantSelector.index_maximal C N h w hInput.wk wi wN
  have maxRaw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (score_represents C N E j h w) (score_represents C N E j h k) max
  have maxFact := le_congr (.eqRefl _) (congrMul (.eqRefl _) (denominator_factor C N E h w)) maxRaw
  have opposite := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (multiple_represents (squaredBudget N) (selectedScore C N) (numerator C N j k) (denominator C N E h k)
      (score_represents C N E j h k)) (GaussianBalancedRadiusSyntax.coefficient_norm_represents C N zero)
    (Prf.hyp0 : Δ ⊢[PRAAx] RationalArgmin.rationalLE (multiple (squaredBudget N) (selectedScore C N)) (constantScore C N))
  exact strict_budget_contradiction _ _ _ _ _ _ _ _ _ maxFact
    (le_congr (by ipra_ring) (.eqRefl _) opposite)
    (factor_budget N h w (le_of_lt (GaussianDominantPlateau.center_bounded C N hInput.wk)) wN) hFail
    (denominator_positive C N E h k) (unit_positive (four*h*w))

theorem dominant_upper (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] upperBound C N := by
  have bounds := GaussianDominantPlateau.winner_bounds C N hInput
  have fit := GaussianBalancedRadiusSearch.fits_degree_at C N (GaussianBalancedRadiusHeight.E C N)
    (GaussianBalancedRadiusSearch.radiusIndex C N) (winner C N)
    (GaussianBalancedRadiusSearch.selected_fits C N hInput) (Prf.andE₁ bounds) (Prf.andE₂ bounds)
  exact RationalArgmin.transitive
    (score_below_initial C N (GaussianBalancedRadiusHeight.E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) (center C N) (winner C N))
    ((GaussianBalancedRadiusValues.fit_iff C N (GaussianBalancedRadiusHeight.E C N)
      (GaussianBalancedRadiusSearch.radiusIndex C N) (winner C N)).iffMp fit)

def selectedNumerator (C N : PTm n) : PTm n := numerator C N (GaussianBalancedRadiusSearch.radiusIndex C N) (winner C N)
def selectedDenominator (C N : PTm n) : PTm n := denominator C N (GaussianBalancedRadiusHeight.E C N) (center C N) (winner C N)

@[simp] theorem subst_selectedNumerator {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (selectedNumerator C N) = selectedNumerator (Syn.subst σ C) (Syn.subst σ N) := by simp [selectedNumerator]
@[simp] theorem subst_selectedDenominator {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (selectedDenominator C N) = selectedDenominator (Syn.subst σ C) (Syn.subst σ N) := by simp [selectedDenominator]

theorem selected_represents (C N : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (selectedScore C N) (ZT.ofNat (selectedNumerator C N)) (selectedDenominator C N) :=
  score_represents C N _ _ _ _

theorem selected_positive (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalLE (selectedScore C N) (fraction zero one)) := by
  refine .impI ?_
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (selected_represents C N).wk (fraction_represents (Γ := Γ) zero one (le_refl one)).wk Prf.hyp0
  have positive := GaussianDominantPlateauValues.winner_scaled_positive C N hInput
  exact le_lt_absurd Fm.bot (le_congr (one_mul _) (zero_mul _) raw) positive.wk

def certificate (C N : PTm n) : Fm PTm n :=
  neg (RationalArgmin.rationalLE (selectedScore C N) (fraction zero one)) ⋏ (upperBound C N ⋏ lowerBound C N)
@[simp] theorem subst_certificate {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    (certificate C N).subst σ = certificate (Syn.subst σ C) (Syn.subst σ N) := by simp [certificate]

theorem dominant_magnitude (C N : PTm n) (hInput : Γ ⊢[PRAAx] input C N) : Γ ⊢[PRAAx] certificate C N :=
  .andI (selected_positive C N hInput) (.andI (dominant_upper C N hInput) (dominant_lower C N hInput))

theorem original_magnitude (C N z : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianTranslatedBalancedRadius.inputContract C N)
    (hPositive : Γ ⊢[PRAAx] le one (GaussianTranslatedBalancedRadius.residual C z)) : Γ ⊢[PRAAx]
    certificate (GaussianRationalTranslation.translated C N z) N :=
  dominant_magnitude _ _ (GaussianTranslatedDominantPlateau.positive_input C N z hInput hPositive)

def output (C N : PTm n) : PTm n := pairT (selectedScore C N) (pairT (constantScore C N)
  (pairT (descentD N) (pairT (selectedNumerator C N) (selectedDenominator C N))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (C N : PTm n) : PTm n := ap2 outputF C N

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (output C N) = output (Syn.subst σ C) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (C N : PTm n) :
    Syn.subst σ (run C N) = run (Syn.subst σ C) (Syn.subst σ N) := by simp [run]

theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] run C N ≐ output C N := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![C,N]
theorem returned_score (C N : PTm n) : Γ ⊢[PRAAx] fstT (run C N) ≐ selectedScore C N :=
  (congrFst (program_at C N)).eqTrans (fst_pair _ _)
theorem returned_constant (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run C N)) ≐ constantScore C N :=
  (congrFst ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_budget (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run C N))) ≐ descentD N :=
  (congrFst ((congrSnd ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_numerator (C N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run C N)))) ≐ selectedNumerator C N :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (C N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run C N)))) ≐ selectedDenominator C N :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at C N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem exact_descent_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((descentD (var 0) ≐ unit (var 0+four*var 0*var 0)) ⋏
      squaredBudget (var 0) ≐ unit (two*var 0+two*four*var 0*var 0)) :=
  closeUniv 1 (.andI (descent_dyadic _) (budget_dyadic _))

theorem dominant_scale_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (two*var 0) ⟶ le (var 2) (var 0) ⟶
      le (pw four (var 0)*restoreFactor (var 1) (var 2)) (squaredBudget (var 0))) :=
  closeUniv 3 (.impI (.impI (factor_budget _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_dominant_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ lowerBound (var 0) (var 1)) :=
  closeUniv 2 (.impI (dominant_lower _ _ Prf.hyp0))

theorem actual_dominant_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ upperBound (var 0) (var 1)) :=
  closeUniv 2 (.impI (dominant_upper _ _ Prf.hyp0))

theorem actual_dominant_magnitude_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input (var 0) (var 1) ⟶ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (dominant_magnitude _ _ Prf.hyp0))

theorem original_dominant_magnitude_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianTranslatedBalancedRadius.inputContract (var 0) (var 1) ⟶
      le one (GaussianTranslatedBalancedRadius.residual (var 0) (var 2)) ⟶
      certificate (GaussianRationalTranslation.translated (var 0) (var 1) (var 2)) (var 1)) :=
  closeUniv 3 (.impI (.impI (original_magnitude _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_magnitude_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run (var 0) (var 1) ≐ output (var 0) (var 1)) ⋏
      ((fstT (run (var 0) (var 1)) ≐ selectedScore (var 0) (var 1)) ⋏
        ((fstT (sndT (run (var 0) (var 1))) ≐ constantScore (var 0) (var 1)) ⋏
          ((fstT (sndT (sndT (run (var 0) (var 1)))) ≐ descentD (var 1)) ⋏
            ((fstT (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ selectedNumerator (var 0) (var 1)) ⋏
              sndT (sndT (sndT (sndT (run (var 0) (var 1))))) ≐ selectedDenominator (var 0) (var 1)))))) :=
  closeUniv 2 (.andI (program_at _ _) (.andI (returned_score _ _) (.andI (returned_constant _ _)
    (.andI (returned_budget _ _) (.andI (returned_numerator _ _) (returned_denominator _ _))))))

end LeanProofs.IPRA.Analysis.GaussianDominantMagnitude
