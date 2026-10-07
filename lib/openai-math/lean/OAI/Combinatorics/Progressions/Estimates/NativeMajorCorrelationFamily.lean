import OAI.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction

namespace OAI

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem uniform_majorPhase_correlation_eq
    {m d : ℕ} {X L : Type} [Fintype X] [DecidableEq X]
    [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (D : RationalFilteredNilmanifold L t e) (T : D.Niltest (fun _ : X => 1))
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (g : integerBox N → ℂ) (heval : ∀ u, g u = T.eval u.val) :
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
      (fun u => majorPhaseSample J d poly Ψ c F β (fun _ => 1) u.val)
      (fun u => star (W.eval N poly u.val) * g u) =
    𝔼 u ∈ integerBox N,
      W.eval N poly u * majorPhaseSample J d poly Ψ c F β T.conjugate.eval u := by
  rw [← FiniteProbabilityWeights.uniformFinset_complexMean (integerBox N) hN]
  unfold FiniteProbabilityWeights.correlation FiniteProbabilityWeights.complexMean
  apply Finset.sum_congr rfl
  intro u _
  dsimp only
  rw [heval u]
  simp only [majorPhaseSample, Niltest.eval_conjugate, star_mul, star_star, mul_one]
  ring

attribute [local instance] NativeSampleModelFamily.lie NativeSampleModelFamily.algebra
  NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd
  NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

theorem exists_native_major_correlation_family
    {m d t : ℕ} {X η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : η → MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (g : η → integerBox N → ℂ) (p : ℝ) (hp : 2 ≤ p)
    (hη : (Fintype.card η : ℝ) ≤ p)
    (native : ∀ j, NativeSampleModel (fun _ : X => 1) t p
      (fun u : integerBox N => u.val) (g j))
    (hcorr : ∀ j, Real.exp (-p) ≤
      ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
        (fun u => majorPhaseSample J d poly Ψ c (F j) β (fun _ => 1) u.val)
        (fun u => star ((W j).eval N poly u.val) * g j u)‖) :
    ∃ common : NativeSampleModelFamily (fun _ : X => 1) t (productNiltestBudget p)
      (fun u : integerBox N => u.val) g,
      ∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u *
          majorPhaseSample J d poly Ψ c (F j) β (common.test j).conjugate.eval u‖ := by
  let common := NativeSampleModelFamily.ofModels native hp hη
  refine ⟨common, ?_⟩
  intro j
  rw [← uniform_majorPhase_correlation_eq J (W j) common.model (common.test j)
    N hN poly Ψ c (F j) β (g j) (common.eval j)]
  exact hcorr j

theorem exists_native_major_correlation_family_of_detections
    {m d t : ℕ} {X η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (N : X → ℕ) (hN : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
    (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (F : η → MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
    (p : ℝ) (hp : 2 ≤ p) (hη : (Fintype.card η : ℝ) ≤ p)
    (hdetected : ∀ j,
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
        (g : integerBox N → ℂ),
        Nonempty (NativeSampleModel (fun _ : X => 1) t p
          (fun u : integerBox N => u.val) g) ∧
        Real.exp (-p) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hN).correlation
            (fun u => majorPhaseSample J d poly Ψ c (F j) β (fun _ => 1) u.val)
            (fun u => star (W.eval N poly u.val) * g u)‖) :
    ∃ (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (g : η → integerBox N → ℂ)
      (common : NativeSampleModelFamily (fun _ : X => 1) t (productNiltestBudget p)
        (fun u : integerBox N => u.val) g),
      ∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u *
          majorPhaseSample J d poly Ψ c (F j) β (common.test j).conjugate.eval u‖ := by
  classical
  choose W g hnative hcorr using hdetected
  let native := fun j => Classical.choice (hnative j)
  obtain ⟨common, hcommon⟩ := exists_native_major_correlation_family J W N hN
    poly Ψ c F β g p hp hη native hcorr
  exact ⟨W, g, common, hcommon⟩

end Erdos3.VectorPolynomial

end

end OAI
