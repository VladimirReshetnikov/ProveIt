import OAI.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

namespace NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def conjugate (W : NormalizedPolynomialTwist X Y periodCap coverCap L) :
    NormalizedPolynomialTwist X Y periodCap coverCap L :=
  { W with
    mask := fun z => star (W.mask z)
    mask_bound := fun z => by simpa only [norm_star] using W.mask_bound z
    smooth := fun z => star (W.smooth z)
    smooth_bound := fun z => by simpa only [norm_star] using W.smooth_bound z
    smooth_lipschitz := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_eq_norm, ← star_sub, norm_star] using W.smooth_lipschitz.dist_le_mul x y }

@[simp] theorem conjugate_eval {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    W.conjugate.eval N poly u = star (W.eval N poly u) := by
  simp only [eval, conjugate, star_mul, mul_comm]
  rfl

end NormalizedPolynomialTwist

theorem normalizedTwist_eval_mem_twistedNativeSampleFunctions
    {X Ω : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) {budget : ℝ} (hbudget : 2 ≤ budget) :
    (fun t => W.eval N poly (sample t)) ∈ twistedNativeSampleFunctions w degree budget sample
      (fun (V : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) t =>
        V.eval N poly (sample t)) := by
  refine Or.inr ⟨W.conjugate, fun _ => 1, ⟨NativeSampleModel.constOne hbudget⟩, ?_⟩
  funext t
  simp only [NormalizedPolynomialTwist.conjugate_eval, star_star, mul_one]

theorem normalizedTwist_star_eval_mem_twistedNativeSampleFunctions
    {X Ω : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (sample : Ω → X → ℤ) (w : X → ℕ) (degree : ℕ) {budget : ℝ} (hbudget : 2 ≤ budget) :
    (fun t => star (W.eval N poly (sample t))) ∈ twistedNativeSampleFunctions w degree budget sample
      (fun (V : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L) t =>
        V.eval N poly (sample t)) := by
  refine Or.inr ⟨W, fun _ => 1, ⟨NativeSampleModel.constOne hbudget⟩, ?_⟩
  funext t
  exact (mul_one _).symm

end Erdos3.VectorPolynomial

end

end OAI
