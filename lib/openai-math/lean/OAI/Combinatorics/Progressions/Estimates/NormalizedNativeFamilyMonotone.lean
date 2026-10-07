import OAI.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer

namespace OAI

section

namespace Erdos3

variable {σ Ω : Type*} {w : σ → ℕ} {degree : ℕ} {p q : ℝ}
  {sample : Ω → σ → ℤ} {f : Ω → ℂ}

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable def NativeSampleModel.mono (F : NativeSampleModel w degree p sample f)
    (hpq : p ≤ q) : NativeSampleModel w degree q sample f where
  L := F.L
  dim := F.dim
  model := F.model
  test := F.test
  norm := F.norm
  complexity := F.complexity.mono hpq
  eval := F.eval

theorem twistedNativeSampleFunctions_mono_of_twist
    {I I' : Type*} (twist : I → Ω → ℂ) (twist' : I' → Ω → ℂ)
    (hpq : p ≤ q) (lift : I → I') (hlift : ∀ i x, twist' (lift i) x = twist i x) :
    twistedNativeSampleFunctions w degree p sample twist ⊆
      twistedNativeSampleFunctions w degree q sample twist' := by
  rintro f (rfl | ⟨i, g, ⟨G⟩, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨lift i, g, ⟨G.mono hpq⟩, by simp only [hlift]⟩

namespace VectorPolynomial
open scoped NNReal

theorem normalizedNativeSampleFunctions_mono
    {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (w : X → ℕ) (degree : ℕ) (sample : Ω → X → ℤ)
    {p q : ℝ} (hpq : p ≤ q) :
    twistedNativeSampleFunctions w degree p sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp p) (Real.exp p)
        ⟨Real.exp p, Real.exp_nonneg _⟩) t => W.eval N poly (sample t)) ⊆
    twistedNativeSampleFunctions w degree q sample
      (fun (W : NormalizedPolynomialTwist X (Σ j, J j) (Real.exp q) (Real.exp q)
        ⟨Real.exp q, Real.exp_nonneg _⟩) t => W.eval N poly (sample t)) := by
  apply twistedNativeSampleFunctions_mono_of_twist _ _ hpq
    (fun W => W.mono (Real.exp_le_exp.mpr hpq) (Real.exp_le_exp.mpr hpq)
      (show (⟨Real.exp p, Real.exp_nonneg _⟩ : ℝ≥0) ≤ ⟨Real.exp q, Real.exp_nonneg _⟩ from
        Real.exp_le_exp.mpr hpq))
  intro W t
  rfl

end VectorPolynomial
end Erdos3

end

end OAI
