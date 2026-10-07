import OAI.Combinatorics.Progressions.Estimates.WeightedPlateauSiteApproximation

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [DecidableEq B] [Fintype α] [DecidableEq α]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource α)
variable (u : B → Fin (n + 1) → Option α → ℤ) (v : B → Fin (n + 1) → Option α → ℕ)

noncomputable def affineCubePlateauCoefficient (K M : ℕ) (rows : Finset (Finset α))
    (k : rows → Fin M) : ℂ :=
  ((K : ℂ) / M) ^ rows.card * ∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M rows k

omit [NeZero M] [DecidableEq B] in
theorem affineCubePlateauCoefficient_sum_le (rows : Finset (Finset α))
    (F : Finset (rows → Fin M)) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M rows k‖) ≤ C) :
    (∑ k : F, ‖affineCubePlateauCoefficient s u v K M rows k‖) ≤ C := by
  rw [← Finset.sum_subtype F (fun _ => Iff.rfl)
    (fun k => ‖affineCubePlateauCoefficient s u v K M rows k‖)]
  simp only [affineCubePlateauCoefficient, norm_mul, norm_pow, norm_div,
    Complex.norm_natCast, ← Finset.mul_sum]
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  apply (mul_le_mul_of_nonneg_left
    ((Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)).trans hcap) (by positivity)).trans
  exact mul_le_of_le_one_left hC hscale

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem affineCubePlateauMixture_model
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset α))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (z : rows → ℤ) :
    (∫ zeta, affineCubePlateauApproximation s u v K H rows (shift zeta) z F ∂p.toMeasure) =
      finiteResidueModeModel (fun k : F => D k) (fun k => a k)
        (fun k => affineCubePlateauCoefficient s u v K M rows k)
        (fun k => plateauModeMixture p H (D k) K (a k) (ω k) shift)
        (fun k => integerGridResidue (D k) z) (fun t => (z t : ℝ) / K) := by
  rw [affineCubePlateauMixture_expansion s u v p hK H rows shift z F D a ω hfreq]
  let term (k : rows → Fin M) := affineCubePlateauCoefficient s u v K M rows k *
    (star (rationalGridPhase (D k) (a k) (integerGridResidue (D k) z)) *
      plateauModeMixture p H (D k) K (a k) (ω k) shift (fun t => (z t : ℝ) / K))
  calc
    _ = ∑ k ∈ F, term k := by
      simp only [term, affineCubePlateauCoefficient, Finset.mul_sum, mul_assoc]
    _ = ∑ k : F, term k := Finset.sum_subtype F (fun _ => Iff.rfl) term
    _ = _ := rfl

theorem exists_affineCube_plateau_site_approximation
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset α))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M rows k‖) ≤ C)
    (W : ℝ≥0) (hW : ∀ k ∈ F, ∀ t, |ω k t| ≤ W)
    {R δ P : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hδP : (δ / (C + 1))⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ N : F → ℕ, (∀ k, (N k : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex α F N) : ℝ) ≤
        F.card * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) ∧
      ∃ (β : PlateauSiteIndex α F N → ℂ)
        (f : (k : PlateauSiteIndex α F N) → Finset α → ZMod (D k.1) → ℝ → ℂ),
        (∑ k, ‖β k‖) ≤ C * Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k u r x, ‖f k u r x‖ ≤ 1) ∧
        (∀ k u r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k u r)) ∧
        ∀ y : Finset α → ℤ, (∀ u, |(y u : ℝ) / K| ≤ R) →
          ‖(∫ zeta, affineCubePlateauApproximation s u v K H rows (shift zeta)
                (fun t => booleanCoefficient y t) F ∂p.toMeasure) -
            ∑ k, β k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / K)‖ ≤ δ := by
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hcap
  have htol : 0 < δ / (C + 1) := div_pos hδ (by positivity)
  obtain ⟨N, hN, hcard, β, f, hβ, hf, hLf, he⟩ :=
    exists_integer_plateau_sum_site_approximation p H K rows (fun k : F => D k)
      (fun k => a k) (fun k => ω k) shift
      (fun k => affineCubePlateauCoefficient s u v K M rows k)
      (affineCubePlateauCoefficient_sum_le s u v rows F hscale hcap)
      W (fun k => hW k k.property) hR htol hP hRP hδP hLP
  refine ⟨N, hN, ?_, β, f, hβ, hf, hLf, ?_⟩
  · simpa only [Fintype.card_coe] using hcard
  · intro y hy
    rw [affineCubePlateauMixture_model s u v p hK H rows F D a ω hfreq shift]
    apply (he y hy).trans
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
    nlinarith only [hC, hδ]

end Erdos3

end

end OAI
