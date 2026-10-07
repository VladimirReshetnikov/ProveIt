import OAI.Combinatorics.Progressions.Probability.CoefficientAmbientDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

theorem exists_coefficient_ambient_fourier_approximation
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hf : ∀ j i d (k : ℤ), f j i d ((k : ℝ) / basisAxisScale (b j) i) =
      basisAxisScale (b j) i * (p j i d k).toReal)
    (hs : ∀ j d x, mixedCoefficientDensity (fun i => c j i d) (fun i => w j i d)
      (fun i => p j i d) x ≠ 0 → ∀ a,
        |normalizedLatticePoint (euclideanSubspace (U j)) (b j) (orthonormalMixedChart (o j) x) a| ≤ 1/4)
    {B L : ℝ≥0} (hB : 1 ≤ B)
    (hcap : ∀ s x, 0 ≤ coefficientAmbientFactor U b o c w f s x ∧
      coefficientAmbientFactor U b o c w f s x ≤ B)
    (hlip : ∀ s, LipschitzWith L (coefficientAmbientFactor U b o c w f s))
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ P)
    (hLP : ((Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m) : ℝ≥0) : ℝ)
      ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (K →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i,
        |(frequency t j d i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) * (B : ℝ)^Fintype.card (CoefficientSlot K m) ∧
      ∀ x, ‖(canonicalCoefficientDensity U b hb o c w p x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  obtain ⟨hbound, hLip⟩ := coefficientAmbientDensity_bounds U b o c w f hB hcap hlip
  have hc : LipschitzWith
      (Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m))
      (fun x => (coefficientAmbientDensity U b o c w f x : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hLip.dist_le_mul x y
  have hbnd (x) : ‖(coefficientAmbientDensity U b o c w f x : ℂ)‖ ≤
      (B^Fintype.card (CoefficientSlot K m) : ℝ≥0) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound x).1, NNReal.coe_pow]
      using (hbound x).2
  obtain ⟨F, inst, frequency, a, hcard, hfreq, hsum, herr⟩ :=
    exists_ambient_torus_fourier_approximation _ _ _ hc hbnd hδ hP hdim hLP hδP
  let _ := inst
  refine ⟨F, inst, fun t => coefficientSlotFrequency (fun s i => frequency t ⟨s, i⟩), a,
    hcard, ?_, hsum, ?_⟩
  · intro t
    exact coefficientSlotFrequency_bound (fun s i => frequency t ⟨s, i⟩) (fun s i => hfreq t ⟨s, i⟩)
  · intro x
    simpa only [coefficientAmbientDensity_eq U b hb o c w f p hf hs x,
      coefficientAmbientTorus_character, coefficientTorusFourierSum] using
      herr (coefficientAmbientTorus U x)

end Erdos3.VectorPolynomial

end

end OAI
