import OAI.Combinatorics.Progressions.Geometry.PreparedFullChartNativeDetection

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

@[simp] theorem physicalGridFactorInput_of_isEmpty
    {X : Type*} {m : ℕ} {J : Fin m → Type*} [IsEmpty (Σ j, J j)]
    (period : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    physicalGridFactorInput period p t = 0 := by
  funext a
  exact isEmptyElim a

namespace NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def eraseEmptyTags
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] [IsEmpty Y] :
    NormalizedPolynomialTwist X Y' periodCap coverCap L where
  modulus := W.modulus
  modulus_pos := W.modulus_pos
  modulus_bound := W.modulus_bound
  cover := W.cover
  cover_pos := W.cover_pos
  cover_bound := W.cover_bound
  mask := W.mask
  mask_bound := W.mask_bound
  smooth := fun z => W.smooth (z.1, 0)
  smooth_bound := fun z => W.smooth_bound _
  smooth_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := W.smooth_lipschitz.dist_le_mul (x.1, 0) (y.1, 0)
    simp only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (show dist x.1 y.1 ≤ dist x y from le_max_left _ _) L.coe_nonneg)

variable [IsEmpty Y]

@[simp] theorem eraseEmptyTags_modulus
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] : (W.eraseEmptyTags Y').modulus = W.modulus := rfl

@[simp] theorem eraseEmptyTags_cover
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] : (W.eraseEmptyTags Y').cover = W.cover := rfl

@[simp] theorem eraseEmptyTags_mask
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] : (W.eraseEmptyTags Y').mask = W.mask := rfl

@[simp] theorem eraseEmptyTags_smooth
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] (z : (X → ℝ) × (Y' → UnitAddCircle)) :
    (W.eraseEmptyTags Y').smooth z = W.smooth (z.1, 0) := rfl

@[simp] theorem eval_eraseEmptyTags
    {m m' : ℕ} {J : Fin m → Type*} {J' : Fin m' → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (J' j)] [IsEmpty (Σ j, J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (p' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ)) (u : X → ℤ) :
    (W.eraseEmptyTags (Σ j, J' j)).eval N p' u = W.eval N p u := by
  simp only [eval, eraseEmptyTags, physicalGridFactorInput_of_isEmpty]
  rfl

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem SampledSliceNativeDetection.retag_of_isEmpty
    {m m' : ℕ} {X Ω T : Type} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype T]
    {Tests : Ω → Type} (J : Fin m → Type) [∀ j, Fintype (J j)]
    [IsEmpty (Σ j, J j)] (J' : Fin m' → Type) [∀ j, Fintype (J' j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (poly' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ))
    (pathLaw : FiniteProbabilityWeights Ω) (physical : Ω → T → X → ℤ)
    (slices : ∀ z, Tests z → Finset T) (weight : ∀ z, Tests z → T → ℂ)
    (degree : ℕ) (pNative α : ℝ)
    (h : SampledSliceNativeDetection J N hbox poly pathLaw physical slices weight
      degree pNative α) :
    SampledSliceNativeDetection J' N hbox poly' pathLaw physical slices weight
      degree pNative α := by
  intro signal hsignal hsupp hlarge
  obtain ⟨W, g, hmodel, hcorr⟩ := h signal hsignal hsupp hlarge
  refine ⟨W.eraseEmptyTags (Σ j, J' j), g, hmodel, ?_⟩
  simpa only [W.eval_eraseEmptyTags N poly poly'] using hcorr

end Erdos3.VectorPolynomial

end

end OAI
