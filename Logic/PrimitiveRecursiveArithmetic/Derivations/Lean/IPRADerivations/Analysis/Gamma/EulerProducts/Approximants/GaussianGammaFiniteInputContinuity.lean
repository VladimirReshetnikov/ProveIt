import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaEulerContinuityReference
import IPRADerivations.Analysis.Exponential.Estimates.Lipschitz.GaussianRationalUniformExponentialLipschitz
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate

/-!
# Uniform input continuity of the actual finite Euler Q_N sampler

The original common finite reference, logarithm queries and scalar
Taylor cutoff are retained. The finite exponential Lipschitz bound
3^M is independent of that cutoff. This gives a single numerical gain
for each disk and positive degree. Original point regularity and one
finite rational gap remove only the auxiliary observation errors.
The two requested observations keep their independent tolerances.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFiniteInputContinuity

open_ipra
open GaussianGammaFiniteApproximantName (qF qData q_regular logExponentF logExponentData)
open GaussianGammaEulerContinuityReference (reference query cutoff headBound head_bound finiteBound original_sample_reference)
open GaussianGammaLogExponentContinuity (logRadius exponentRadius exponent_bound exponent_distance distanceBudget)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_from_model_comparison)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def gain (R N : PTm n) : PTm n :=
  GaussianGammaEulerHeadContinuity.gain R N*finiteBound R N+
    headBound R N*finiteBound R N*logRadius N
def loss (R N : PTm n) : PTm n :=
  num 4+num 6*headBound R N+two*headBound R N*finiteBound R N*R
def input (z w R B A D N : PTm n) : Fm PTm n :=
  le one N ⋏ GaussianGammaEulerHeadContinuity.input z w R B A D
ipra_subst gain [finiteBound]
ipra_subst loss [finiteBound]
ipra_subst input
@[simp] theorem subst_finite_data {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (qData z B N) = qData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [qData,GaussianGammaFiniteApproximantName.approximantData,
    GaussianGammaFiniteApproximantName.exponentialInputData,logExponentData]

/-- The same actual finite reference has a gain independent of its
query precision and its actual Taylor cutoff. -/
theorem reference_distance (r z w R B A D N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B A D N) : Γ ⊢[PRAAx]
    distanceBounded (reference r z R B N) (reference r w R B N)
      (gain R N*A*unit (query r R N)+two*headBound R N*finiteBound R N*D*R)
      (D*unit (query r R N)) := by
  let j := query r R N
  have hN := h.andE₁
  have hB := h.andE₂.andE₁
  have hD := h.andE₂.andE₂.andE₁
  have hz := h.andE₂.andE₂.andE₂.andE₁
  have hw := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hd := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have den := positive_product _ _ hD (unit_positive j)
  have heads := GaussianGammaEulerHeadContinuity.returned_head_distance z w R B A D N h.andE₂
  have first := distance_radius_mono _ _ _ _
    (GaussianGammaEulerHeadContinuity.gain R N*A*unit j) (D*unit j) hD den
    (le_of_eq_add (d := zero) (by ipra_ring)) heads
  have ez := exponent_bound j z R B N hN hB hz
  have ew := exponent_bound j w R B N hN hB hw
  have second := GaussianRationalUniformExponentialLipschitz.scalar_sum_lipschitz _ _ (exponentRadius R N)
    (distanceBudget j R A D N) (D*unit j) (cutoff r R N) den ez ew
    (exponent_distance j z w R B A D N hN hB hD hz hd)
  have raw := GaussianNameArithmetic.product_distance _ _ _ _
    (GaussianGammaEulerHeadContinuity.gain R N*A*unit j)
    (finiteBound R N*distanceBudget j R A D N) (D*unit j)
    (finiteBound R N) (headBound R N) den first second
    (GaussianPositiveExponentialMajorant.disk_bound _ _ _ ez)
    (head_bound w R B N (.andI hN (.andI hB hw)))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold gain distanceBudget; ipra_ring) (.eqRefl _) raw

theorem reference_distance_wide (r z w R B A D N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B A D N) : Γ ⊢[PRAAx]
    distanceBounded (reference r z R B N) (reference r w R B N)
      (gain R N*A*unit r+two*headBound R N*finiteBound R N*D*R) (D*unit r) := by
  have later : Γ ⊢[PRAAx] le r (query r R N) :=
    le_trans (le_add_right r (num 4)) (le_add_right (r+num 4) _)
  have order := GaussianExponentialReference.unit_monotone later
  have grow := mul_le_mul_right (two*headBound R N*finiteBound R N*D*D*R) order
  have sum := add_le_add₂ (le_refl (Γ := Γ) (gain R N*A*unit (query r R N)*D*unit r)) grow
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ h.andE₂.andE₂.andE₁ (unit_positive _))
    (positive_product _ _ h.andE₂.andE₂.andE₁ (unit_positive _))
    (le_congr (by ipra_ring) (by ipra_ring) sum) (reference_distance r z w R B A D N h)

/-- Both samples and both finite references are actual unchanged programs.
The only error left beyond gain times input distance is loss*2^-t. -/
theorem diagonal_distance (t z w R B A D N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B A D N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 qF t (qData z B N)) (ap2 qF t (qData w B N))
      (gain R N*A*unit t+loss R N*D) (D*unit t) := by
  let H := headBound R N
  let U := unit t
  let L := two+num 3*H
  have hD := h.andE₂.andE₂.andE₁
  have hu := unit_positive (Γ := Γ) t
  have den := positive_product _ _ hD hu
  have zi : Γ ⊢[PRAAx] GaussianGammaEulerContinuityReference.input z R B N :=
    .andI h.andE₁ (.andI h.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁)
  have wi : Γ ⊢[PRAAx] GaussianGammaEulerContinuityReference.input w R B N :=
    .andI h.andE₁ (.andI h.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₁)
  have leftRaw := distance_radius_mono _ _ _ _ L U (positive_product _ _ hu hu) hu
    (le_of_eq_add (d := zero) (by dsimp only [L,H,U]; ipra_ring))
    (original_sample_reference t t z R B N zi)
  have rightRaw := distance_radius_mono _ _ _ _ L U (positive_product _ _ hu hu) hu
    (le_of_eq_add (d := zero) (by dsimp only [L,H,U]; ipra_ring))
    (original_sample_reference t t w R B N wi)
  have joined := distance_from_model_comparison _ (D*U) U L L den hu
    leftRaw (reference_distance_wide t z w R B A D N h) rightRaw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ den hu) den
    (le_of_eq_add (d := zero) (by dsimp only [L,H,U,loss]; ipra_ring)) joined

theorem diagonal_envelope (z w R B A D N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B A D N) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope qF qF (qData z B N) (qData w B N) (gain R N*A) D (loss R N) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift B)
      (Syn.shift A) (Syn.shift D) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,Syn.shift,subst_finite_data,subst_gain,subst_loss,PTm.subst_mul] using
      diagonal_distance (var 0) (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift D) (Syn.shift N) hs

theorem original_independent_rate (z w R B A D N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B A D N) : Γ ⊢[PRAAx]
    independentRate qF qF (qData z B N) (qData w B N) (gain R N*A) D :=
  GaussianNamedLipschitzRate.independent_rate qF qF _ _ _ _ (loss R N)
    h.andE₂.andE₂.andE₁ (q_regular z B N h.andE₁) (q_regular w B N h.andE₁) (diagonal_envelope z w R B A D N h)

theorem original_observations (p q z w R B A D N : PTm n)
    (h : Γ ⊢[PRAAx] input z w R B A D N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 qF p (qData z B N)) (ap2 qF q (qData w B N))
      (rateNumerator (gain R N*A) D p q) (rateDenominator D p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_independent_rate z w R B A D N h)

theorem original_finite_Q_uniform_input_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      independentRate qF qF (qData (var 0) (var 3) (var 6)) (qData (var 1) (var 3) (var 6))
        (gain (var 2) (var 6)*var 4) (var 5)) :=
  closeUniv 7 (.impI (original_independent_rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFiniteInputContinuity
