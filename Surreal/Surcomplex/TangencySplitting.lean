import Surreal.Surcomplex.AmplitudeIntersection
import Surreal.Surcomplex.AcosEndpointSeries
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Square-root splitting of actual tangent intersections

The two finite-angle branches in `trigonometry:thm:tangency` satisfy the
literal expansion `trigonometry:eq:tangency`. Their actual lift separation
has half the defect valuation, and the first-harmonic derivative magnitude
is the stated amplitude times the square root. The amplitude may have any
surreal scale. The perturbation assertions are separate results.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private theorem infinitesimal_pos_lt_one {τ : SignSequence.{u}}
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) : τ < 1 := by
  have he := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt τ).mp hi 1 (by norm_num)
  simpa only [map_one, abs_of_pos hp] using he

/-- A positive infinitesimal defect lies strictly inside the cosine range. -/
theorem tangency_parameter_mem (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    1 - τ ∈ Set.Icc (-1) 1 := by
  have ht := infinitesimal_pos_lt_one hp hi
  constructor <;> linarith

/-- The actual finite inverse-cosine offset from a tangent angle. -/
def tangencyOffset (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) : SignSequence.FiniteElement.{u} :=
  arccos ⟨1 - τ, tangency_parameter_mem τ hp hi⟩

/-- The branch with positive offset, as an actual finite angle. -/
def tangencyBranchPlus (φ : SignSequence.FiniteElement.{u}) (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) : SignSequence.FiniteElement.{u} :=
  φ + tangencyOffset τ hp hi

/-- The branch with negative offset, as an actual finite angle. -/
def tangencyBranchMinus (φ : SignSequence.FiniteElement.{u}) (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) : SignSequence.FiniteElement.{u} :=
  φ - tangencyOffset τ hp hi

theorem tangencyOffset_val (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    (tangencyOffset τ hp hi).val = arccosFunction (1 - τ) :=
  (arccosFunction_eq ⟨1 - τ, tangency_parameter_mem τ hp hi⟩).symm

@[simp] theorem finiteCos_tangencyOffset (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    finiteCos (tangencyOffset τ hp hi) = 1 - τ :=
  finiteCos_arccos _

/-- Both displayed branches solve the actual harmonic equation. -/
theorem tangency_branch_solutions (A B : SignSequence.{u}) (h : 0 < A ^ 2 + B ^ 2)
    (φ : SignSequence.FiniteElement.{u})
    (hc : finiteCos φ = A / SignSequence.sqrt (A ^ 2 + B ^ 2))
    (hs : finiteSin φ = B / SignSequence.sqrt (A ^ 2 + B ^ 2))
    (τ : SignSequence.{u}) (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    A * finiteCos (tangencyBranchPlus φ τ hp hi) +
        B * finiteSin (tangencyBranchPlus φ τ hp hi) =
        SignSequence.sqrt (A ^ 2 + B ^ 2) * (1 - τ) ∧
      A * finiteCos (tangencyBranchMinus φ τ hp hi) +
        B * finiteSin (tangencyBranchMinus φ τ hp hi) =
        SignSequence.sqrt (A ^ 2 + B ^ 2) * (1 - τ) := by
  have hρ := (SignSequence.sqrt_pos h).ne'
  constructor
  · rw [amplitude_phase A B _ hρ φ _ hc hs]
    simp only [tangencyBranchPlus, add_sub_cancel_left, finiteCos_tangencyOffset]
  · rw [amplitude_phase A B _ hρ φ _ hc hs]
    rw [show tangencyBranchMinus φ τ hp hi - φ = -tangencyOffset τ hp hi by
      dsimp only [tangencyBranchMinus]; abel]
    rw [finiteCos_neg, finiteCos_tangencyOffset]

/-- The two nearby representatives belong to distinct classes modulo ordinary full turns. -/
theorem tangency_branch_classes_ne (φ : SignSequence.FiniteElement.{u})
    (τ : SignSequence.{u}) (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    finiteAngleClass (tangencyBranchPlus φ τ hp hi) ≠
      finiteAngleClass (tangencyBranchMinus φ τ hp hi) := by
  intro he
  have he' := (shifted_classes_eq_iff φ (tangencyOffset τ hp hi)).mp he
  rw [finiteCos_tangencyOffset, abs_of_pos (sub_pos.mpr (infinitesimal_pos_lt_one hp hi))] at he'
  linarith

private theorem finite_two : SignSequence.IsFinite (2 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)

/-- The offsets are actual infinitesimals, so these are branches near the prescribed phase. -/
theorem infinitesimal_tangencyOffset (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.IsInfinitesimal (tangencyOffset τ hp hi).val := by
  obtain ⟨R, hR, _, he⟩ := arccosFunction_endpoint_leading_factor τ hp hi
  rw [tangencyOffset_val, he]
  exact SignSequence.infinitesimal_mul_finite
    (SignSequence.infinitesimal_sqrt (by positivity : 0 ≤ 2 * τ)
      (SignSequence.finite_mul_infinitesimal finite_two hi)) hR

/-- The source's quadratic normalized expansion has an exact finite cubic remainder. -/
theorem tangency_offset_expansion (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 5 / 896 ∧
      (tangencyOffset τ hp hi).val = SignSequence.sqrt (2 * τ) *
        (1 + τ / 12 + 3 * τ ^ 2 / 160 + τ ^ 3 * R) := by
  obtain ⟨E, hE, _, he⟩ := arccosFunction_endpoint_expansion τ hp hi
  have htf := SignSequence.finite_of_infinitesimal hi
  have hcf : SignSequence.IsFinite (5 / 896 : SignSequence.{u}) := by
    simpa only [map_div₀, map_ofNat] using SignSequence.finite_ofReal (5 / 896 : ℝ)
  have hcs : SignSequence.standardPart (5 / 896 : SignSequence.{u}) = 5 / 896 := by
    simpa only [map_div₀, map_ofNat] using SignSequence.standardPart_ofReal (5 / 896 : ℝ)
  refine ⟨5 / 896 + τ * E, SignSequence.finite_add hcf (SignSequence.finite_mul htf hE), ?_, ?_⟩
  · rw [SignSequence.standardPart_add hcf (SignSequence.finite_mul htf hE), hcs,
      SignSequence.standardPart_mul htf hE,
      (SignSequence.standardPart_eq_zero_iff htf).mpr hi, zero_mul, add_zero]
  · rw [tangencyOffset_val, he]
    ring

/-- Both actual branch values satisfy `trigonometry:eq:tangency`, with the same finite tail. -/
theorem tangency_branch_expansion (φ : SignSequence.FiniteElement.{u}) (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    ∃ R : SignSequence.{u}, SignSequence.IsFinite R ∧ SignSequence.standardPart R = 5 / 896 ∧
      (tangencyBranchPlus φ τ hp hi).val = φ.val + SignSequence.sqrt (2 * τ) *
        (1 + τ / 12 + 3 * τ ^ 2 / 160 + τ ^ 3 * R) ∧
      (tangencyBranchMinus φ τ hp hi).val = φ.val - SignSequence.sqrt (2 * τ) *
        (1 + τ / 12 + 3 * τ ^ 2 / 160 + τ ^ 3 * R) := by
  obtain ⟨R, hR, hr, he⟩ := tangency_offset_expansion τ hp hi
  refine ⟨R, hR, hr, ?_, ?_⟩
  · change φ.val + (tangencyOffset τ hp hi).val = _
    rw [he]
  · change φ.val - (tangencyOffset τ hp hi).val = _
    rw [he]

/-- The separation is an exact actual-field identity between the displayed finite lifts. -/
theorem tangency_separation_eq (φ : SignSequence.FiniteElement.{u}) (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    (tangencyBranchPlus φ τ hp hi).val - (tangencyBranchMinus φ τ hp hi).val =
      2 * arccosFunction (1 - τ) := by
  change (φ.val + (tangencyOffset τ hp hi).val) -
    (φ.val - (tangencyOffset τ hp hi).val) = _
  rw [tangencyOffset_val]
  ring

private theorem valuation_two : SignSequence.valuation (2 : SignSequence.{u}) = 0 := by
  simpa only [map_ofNat] using
    (SignSequence.valuation_ofReal_of_ne_zero (by norm_num : (2 : ℝ) ≠ 0) :
      SignSequence.valuation (SignSequence.ofReal 2 : SignSequence.{u}) = 0)

/-- The literal separation valuation is half the nonzero defect's finite valuation exponent. -/
theorem valuation_tangency_separation (φ : SignSequence.FiniteElement.{u}) (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.valuation
      ((tangencyBranchPlus φ τ hp hi).val - (tangencyBranchMinus φ τ hp hi).val) =
      ((-SignSequence.leadingExponent τ / 2 : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  rw [tangency_separation_eq, SignSequence.valuation_mul, valuation_two, zero_add,
    valuation_arccosFunction_one_sub τ hp hi]

/-- The same separation valuation in intrinsic additive-valuation notation. -/
theorem two_nsmul_valuation_tangency_separation (φ : SignSequence.FiniteElement.{u})
    (τ : SignSequence.{u}) (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    2 • SignSequence.valuation
      ((tangencyBranchPlus φ τ hp hi).val - (tangencyBranchMinus φ τ hp hi).val) =
      SignSequence.valuation τ := by
  rw [tangency_separation_eq, SignSequence.valuation_mul, valuation_two, zero_add]
  exact two_nsmul_valuation_arccosFunction_one_sub τ hp hi

/-- The near-tangent discriminant factors at an arbitrary amplitude scale. -/
theorem sqrt_tangency_discriminant (A B : SignSequence.{u}) (h : 0 < A ^ 2 + B ^ 2)
    (τ : SignSequence.{u}) (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    SignSequence.sqrt
      (lineCircleDiscriminant A B (SignSequence.sqrt (A ^ 2 + B ^ 2) * (1 - τ))) =
      SignSequence.sqrt (A ^ 2 + B ^ 2) * SignSequence.sqrt (τ * (2 - τ)) := by
  have ht : 0 ≤ τ * (2 - τ) :=
    mul_nonneg hp.le (by linarith [infinitesimal_pos_lt_one hp hi])
  apply SignSequence.sqrt_eq_of_nonneg_sq
    (mul_nonneg (SignSequence.sqrt_nonneg _) (SignSequence.sqrt_nonneg _))
  rw [mul_pow, SignSequence.sqrt_sq h.le, SignSequence.sqrt_sq ht]
  dsimp only [lineCircleDiscriminant]
  rw [mul_pow, SignSequence.sqrt_sq h.le]
  ring

/-- Every solution at the near-tangent level has the asserted derivative magnitude. -/
theorem firstHarmonic_tangency_derivative_abs (A B : SignSequence.{u})
    (h : 0 < A ^ 2 + B ^ 2) (τ : SignSequence.{u})
    (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ)
    (θ : SignSequence.FiniteElement.{u})
    (hθ : A * finiteCos θ + B * finiteSin θ =
      SignSequence.sqrt (A ^ 2 + B ^ 2) * (1 - τ)) :
    |B * finiteCos θ - A * finiteSin θ| =
      SignSequence.sqrt (A ^ 2 + B ^ 2) * SignSequence.sqrt (τ * (2 - τ)) := by
  rw [firstHarmonic_derivative_abs A B _ θ hθ, sqrt_tangency_discriminant A B h τ hp hi]

/-- The actual derivative magnitude at each of the two displayed splitting branches. -/
theorem tangency_branch_derivative_abs (A B : SignSequence.{u}) (h : 0 < A ^ 2 + B ^ 2)
    (φ : SignSequence.FiniteElement.{u})
    (hc : finiteCos φ = A / SignSequence.sqrt (A ^ 2 + B ^ 2))
    (hs : finiteSin φ = B / SignSequence.sqrt (A ^ 2 + B ^ 2))
    (τ : SignSequence.{u}) (hp : 0 < τ) (hi : SignSequence.IsInfinitesimal τ) :
    |B * finiteCos (tangencyBranchPlus φ τ hp hi) -
        A * finiteSin (tangencyBranchPlus φ τ hp hi)| =
        SignSequence.sqrt (A ^ 2 + B ^ 2) * SignSequence.sqrt (τ * (2 - τ)) ∧
      |B * finiteCos (tangencyBranchMinus φ τ hp hi) -
        A * finiteSin (tangencyBranchMinus φ τ hp hi)| =
        SignSequence.sqrt (A ^ 2 + B ^ 2) * SignSequence.sqrt (τ * (2 - τ)) := by
  have he := tangency_branch_solutions A B h φ hc hs τ hp hi
  exact ⟨firstHarmonic_tangency_derivative_abs A B h τ hp hi _ he.1,
    firstHarmonic_tangency_derivative_abs A B h τ hp hi _ he.2⟩

/-- The perturbation `e=-τ` merges the two branches into one actual angle class. -/
theorem tangency_merge_at_canceling_perturbation (A B ρ : SignSequence.{u}) (hρ : 0 < ρ)
    (φ : SignSequence.FiniteElement.{u})
    (hc : finiteCos φ = A / ρ) (hs : finiteSin φ = B / ρ) (τ : SignSequence.{u}) :
    ∃! θ : FiniteAngleClass.{u}, angleClassHarmonic A B θ = ρ * (1 - (τ + -τ)) := by
  simpa only [add_neg_cancel, sub_zero, mul_one] using
    amplitude_unique_solution A B ρ ρ hρ φ hc hs (abs_of_pos hρ)

/-- A perturbation below `-τ` destroys all actual finite-angle intersections. -/
theorem tangency_no_solution_beyond_canceling_perturbation (A B ρ : SignSequence.{u})
    (hρ : 0 < ρ) (φ : SignSequence.FiniteElement.{u})
    (hc : finiteCos φ = A / ρ) (hs : finiteSin φ = B / ρ)
    (τ e : SignSequence.{u}) (he : e < -τ) (θ : FiniteAngleClass.{u}) :
    angleClassHarmonic A B θ ≠ ρ * (1 - (τ + e)) := by
  apply amplitude_no_solution A B _ ρ hρ φ hc hs _ θ
  have hb : ρ < ρ * (1 - (τ + e)) := by
    nlinarith [mul_pos hρ (show 0 < -(τ + e) by linarith)]
  rw [abs_of_pos (hρ.trans hb)]
  exact hb

end
end Surreal.Surcomplex
