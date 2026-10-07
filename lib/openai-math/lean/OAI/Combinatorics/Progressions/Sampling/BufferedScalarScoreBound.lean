import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative
import OAI.Combinatorics.Progressions.Estimates.WeightedPatchReparam
import OAI.Combinatorics.Progressions.Lattices.BufferedIntegerLift

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def bufferedScalarScore {Ω : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) (u : Ω) : ℝ :=
  (f u - lam) * χ.value (fun i => x u i - (nearestIntegerLift (x u) i : ℝ)) *
    T u (nearestIntegerLift (x u))

theorem bufferedScalarScore_weighted {Ω : Type*} [Fintype Ω] {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T G : Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) :
    (𝔼 u, G u (nearestIntegerLift (x u)) * bufferedScalarScore χ x T f lam u) =
      𝔼 u, (f u - lam) * ∑' β,
        χ.value (fun i => x u i - (β i : ℝ)) * G u β * T u β := by
  apply Finset.expect_congr rfl
  intro u _
  have h := χ.buffered_sum_eq_nearest (x u) (fun β => G u β * T u β)
  simp only [← mul_assoc] at h
  rw [h]
  dsimp only [bufferedScalarScore]
  ring

theorem buffered_model_score_transfer {Ω U I : Type*}
    [Fintype Ω] [Fintype U] [Fintype I] {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T G : Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) (ψ : U → Ω)
    (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ x T f lam u : ℂ)) = (∑ i, c i • J i) + e)
    {M η α β S : ℝ} (hη : 0 ≤ η) (hc : (∑ i, ‖c i‖) ≤ M)
    (hatom : ∀ i, ‖(𝔼 u, (G u (nearestIntegerLift (x u)) : ℂ) * J i u) -
      (𝔼 a, J i (ψ a))‖ ≤ η)
    (heA : ‖𝔼 u, (G u (nearestIntegerLift (x u)) : ℂ) * e u‖ ≤ α)
    (heB : ‖𝔼 a, e (ψ a)‖ ≤ β)
    (hscore : S ≤ 𝔼 a, bufferedScalarScore χ x T f lam (ψ a)) :
    S - (M * η + α + β) ≤ 𝔼 u, (f u - lam) * ∑' b,
      χ.value (fun i => x u i - (b i : ℝ)) * G u b * T u b := by
  have h := finite_weighted_model_score_transfer id ψ (fun u => G u (nearestIntegerLift (x u)))
    (fun _ => 1) (bufferedScalarScore χ x T f lam) e J c hmodel hη hc
    (by simpa only [id_eq, Complex.ofReal_one, one_mul] using hatom) heA
    (by simpa only [Complex.ofReal_one, one_mul] using heB)
    (by simpa only [one_mul] using hscore)
  simpa only [id_eq, bufferedScalarScore_weighted] using h

end Erdos3

end

section

namespace Erdos3

theorem abs_bufferedScalarScore_le_one {Ω : Type*} {m : ℕ}
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (T : Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ)
    (hf : ∀ u, f u ∈ Set.Icc (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hT : ∀ u b, T u b ∈ Set.Icc (0 : ℝ) 1) (u : Ω) :
    |bufferedScalarScore χ x T f lam u| ≤ 1 := by
  have hdiff : |f u - lam| ≤ 1 := abs_le.mpr ⟨by linarith [(hf u).1, hlam.2],
    by linarith [(hf u).2, hlam.1]⟩
  unfold bufferedScalarScore
  rw [abs_mul, abs_mul, abs_of_nonneg (χ.nonneg _), abs_of_nonneg (hT u _).1]
  exact (mul_le_of_le_one_left (hT u _).1
    ((mul_le_of_le_one_left (χ.nonneg _) hdiff).trans (χ.le_one _))).trans (hT u _).2

theorem norm_bufferedWeightedPatchScore_le_exp
    {Ω σ : Type*} {m s d : ℕ} {w : σ ⊕ Fin m → ℕ}
    (B : WeightedParameterPatch (σ ⊕ Fin m) w s d)
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ) (point : Ω → σ → ℝ)
    (f : Ω → ℝ) (lam : ℝ) {p : ℝ} (hp : 0 ≤ p)
    (hf : ∀ u, f u ∈ Set.Icc (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (u : Ω) :
    ‖(bufferedScalarScore χ x
      (fun u b => B.value (Sum.elim (point u) (fun i => (b i : ℝ)))) f lam u : ℂ)‖ ≤
        Real.exp p := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (abs_bufferedScalarScore_le_one χ x _ f lam hf hlam
    (fun u b => B.value_mem_Icc _) u).trans (Real.one_le_exp hp)

end Erdos3

end

end OAI
