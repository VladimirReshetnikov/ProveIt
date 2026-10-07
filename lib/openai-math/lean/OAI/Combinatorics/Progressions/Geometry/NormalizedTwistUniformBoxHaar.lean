import OAI.Combinatorics.Progressions.Fourier.MajorPhaseLowFourierExtraction
import OAI.Combinatorics.Progressions.Fourier.NormalizedTwistSingleSiteFourierHaar

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_normalizedTwist_uniform_progression_haar_comparison (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X : Type} [Fintype X] [DecidableEq X]
      {J : Fin m → Type} [∀ j, Fintype (J j)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
      [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)),
      (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) →
      (∀ j α, coefficients (poly j) α ∈ U j) →
      ∀ {periodCap coverCap : ℝ} {L : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      (residue : X → ZMod W.modulus) (center : X → ℝ)
      {η Q p Rrank : ℝ}, 0 < η → 0 ≤ Q →
      (Fintype.card (Σ j, J j) : ℝ) ≤ Q →
      (L : ℝ) ≤ Real.exp Q → η⁻¹ ≤ Real.exp Q →
      2 ≤ p → (2 * Q + 2) ^ 4 ≤ p →
      (W.cover : ℝ) ≤ Real.exp p →
      ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ Real.exp p →
      ∀ (start : X → ℤ) (K : ℝ), 1 ≤ K → K ≤ Real.exp p →
      ∀ (N : X → ℝ), (∀ i, 0 < N i) →
      ∀ (origin : X → ℤ) (lengths : X → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, N i ≤ K * (q : ℝ) * (lengths i : ℝ)) →
      (Fintype.card X : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1) N Rrank (U j) (poly j)) →
      ‖(𝔼 x ∈ translatedIntegerBox origin lengths,
        W.frozenTorus residue center (physicalGridFactorInput W.cover poly
          (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ)))) -
        W.frozenSingleSiteHaarReference U ν residue center‖ ≤
        2 * η + Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) := by
  obtain ⟨C, hC, hfourier⟩ := exists_normalizedTwist_uniform_box_fourier_comparison m
  refine ⟨C, hC, ?_⟩
  intro X _ _ J _ U ν _ _ poly hp hm periodCap coverCap L W residue center
    η Q p Rrank hη hQ hdim hL hηQ hp2 hfreq hcover q hq hqp start K hK hKp N hN
    origin lengths hlengths hNL hX hlarge hRrank hrank
  obtain ⟨F, inst, frequency, coeff, _, hfreqB, hmass, herr⟩ :=
    exists_ambient_torus_fourier_approximation (W.frozenTorus residue center) L 1
      (W.frozenTorus_lipschitz residue center) (W.norm_frozenTorus_le residue center)
      hη hQ hdim hL hηQ
  let := inst
  let : ∀ i, NeZero (lengths i) := fun i => ⟨(hlengths i).ne'⟩
  let μ := Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))
  let chart : EuclideanJetLayers U (fun _ => Unit) → (Σ j, J j) → UnitAddCircle :=
    fun y a => coveredJetAmbientTorus U 1 y ⟨a.1, (), a.2⟩
  let f := W.frozenTorus residue center
  let g : ((Σ j, J j) → UnitAddCircle) → ℂ :=
    fun y => ∑ b, coeff b * ambientIntegerCharacter (frequency b) y
  let point (x : X → ℤ) := physicalGridFactorInput W.cover poly
    (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
  have hfg (y) : ‖f y - g y‖ ≤ η := herr y
  have hmean : ‖(𝔼 x ∈ translatedIntegerBox origin lengths, f (point x)) -
      (𝔼 x ∈ translatedIntegerBox origin lengths, g (point x))‖ ≤ η := by
    rw [← Finset.expect_sub_distrib]
    exact (RCLike.norm_expect_le (K := ℂ)).trans
      (Finset.expect_le (translatedIntegerBox_nonempty lengths origin) (fun x _ => hfg _))
  have hf : Integrable (fun y => f (chart y)) μ :=
    W.frozenSingleSiteHaarReference_integrable U ν residue center
  have hgi (b : F) : Integrable (fun y => coeff b * ambientIntegerCharacter (frequency b) (chart y)) μ :=
    (singleSiteHaar_ambientIntegerCharacter_integrable U ν (frequency b)).const_mul _
  have hg : Integrable (fun y => g (chart y)) μ := integrable_finsetSum _ (fun b _ => hgi b)
  have hint : ‖(∫ y, g (chart y) ∂μ) - ∫ y, f (chart y) ∂μ‖ ≤ η :=
    probability_integral_approximation μ _ _ hg hf (fun y => by
      simpa only [norm_sub_rev] using hfg (chart y))
  have hge : (∫ y, g (chart y) ∂μ) =
      ∑ b, coeff b * (if ∀ j, U j ≤ LinearMap.ker
        (integerRowLinear (fun i => frequency b ⟨j, i⟩)) then 1 else 0) := by
    rw [show (fun y => g (chart y)) =
      (fun y => ∑ b, coeff b * ambientIntegerCharacter (frequency b) (chart y)) from rfl,
       integral_finsetSum _ (fun b _ => hgi b)]
    apply Finset.sum_congr rfl
    intro b _
    rw [integral_const_mul]
    exact congrArg (coeff b * ·) (singleSiteHaar_ambientIntegerCharacter_integral U ν (frequency b))
  have hcomp := hfourier W.cover W.cover_pos frequency coeff poly hp U hm p Rrank hp2 hcover
    (fun b i => (hfreqB b i).trans (Real.exp_le_exp.mpr hfreq)) q hq hqp start K hK hKp
    N hN origin lengths hlengths hNL hX hlarge hRrank hrank
  have hgpoint (x) : g (point x) = ∑ b, coeff b *
      (Real.fourierChar (MvPolynomial.eval
        (fun i => (start i : ℝ) + (q : ℝ) * (x i : ℝ))
        (normalizedTwistFrequencyPolynomial W.cover (frequency b) poly)) : ℂ) := by
    simp only [g, point, ambientIntegerCharacter, physicalGrid_character_eq_polynomial_phase]
  rw [← hge] at hcomp
  simp_rw [← hgpoint] at hcomp
  have hmass' : (∑ b, ‖coeff b‖) * Real.exp (-p) ≤
      Real.exp (2 * Q * (2 * Q + 2) ^ 4 - p) := by
    calc
      _ ≤ Real.exp (2 * Q * (2 * Q + 2) ^ 4) * Real.exp (-p) :=
        mul_le_mul_of_nonneg_right (by simpa using hmass) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; rfl
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 x ∈ translatedIntegerBox origin lengths, f (point x))
    (𝔼 x ∈ translatedIntegerBox origin lengths, g (point x)) (∫ y, f (chart y) ∂μ)
  have ht' := norm_sub_le_norm_sub_add_norm_sub
    (𝔼 x ∈ translatedIntegerBox origin lengths, g (point x))
    (∫ y, g (chart y) ∂μ) (∫ y, f (chart y) ∂μ)
  change ‖(𝔼 x ∈ translatedIntegerBox origin lengths, f (point x)) -
    ∫ y, f (chart y) ∂μ‖ ≤ _
  linarith [hcomp.trans hmass']

end Erdos3.VectorPolynomial

end

end OAI
