import OAI.Combinatorics.Progressions.Geometry.AllocatedRowSlicedIdealCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

variable (rowSets : Fin m → Finset (Finset α))

local notation "jets" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "siteRadius" => allocatedRowSlicedSiteRadius rowSets
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "hLayer" => layerSamplerDegree I n

variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

theorem allocatedRowSlicedIdealCutoff_complex_mul
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ a, |v a| ≤ (siteRadius : ℝ)) → χ v = 1)
    (z : AllocatedLongJetRows B U b S jets) :
    (∏ s : Finset α, (χ (allocatedRowIdealCoordinates B U b S rowSets z s) : ℂ)) *
      (allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) =
      (allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) := by
  by_cases hz : allocatedRowSlicedIdeal B U b S rowSets δ center width
      (allocatedLongJetRealCoordinates B U b S z) = 0
  · rw [hz, Complex.ofReal_zero, mul_zero]
  · have hp : (∏ s : Finset α, (χ (allocatedRowIdealCoordinates B U b S rowSets z s) : ℂ)) = 1 := by
      apply Finset.prod_eq_one
      intro s _
      rw [hone _ (allocatedRowSlicedIdealCoordinates_bound B U b S rowSets δ hδ hδ1 center width hw z hz s),
        Complex.ofReal_one]
    rw [hp, one_mul]

theorem allocatedRowSlicedIdealApproximation_error {T : Type*} [Fintype T]
    (hR : ∀ j, 0 < R j) (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    (χ : (LayerSamplerAxis I n → ℝ) → ℝ)
    (hone : ∀ v, (∀ a, |v a| ≤ (siteRadius : ℝ)) → χ v = 1)
    (a : T → ℂ) (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) (ε : ℝ)
    (herr : ∀ v : Finset α → LayerSamplerAxis I n → ℝ,
      ‖(∏ s, (χ (v s) : ℂ)) * (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α) hLayer grid
          (fun a => (Subtype.val : jets a.val.1 → Finset α)) δ center width
          (booleanSiteJets (fun a : {a // ¬grid a} => (Subtype.val : jets a.val.1 → Finset α))
            (fun s d => v s d.val)) : ℂ) - ∑ i, a i * ∏ s, f i s (v s)‖ ≤ ε)
    (z : AllocatedLongJetRows B U b S jets) :
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
    ‖(volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
      ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)‖ ≤ ε ∧
    ‖(allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
      (∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ ≤ ε / volume := by
  intro volume
  have hdensity := congrArg Complex.ofReal (allocatedRowSlicedIdealCoordinates_density B U b S rowSets hR δ center width z)
  simp only [Complex.ofReal_mul] at hdensity
  have hcutoff := allocatedRowSlicedIdealCutoff_complex_mul B U b S rowSets center width δ hδ hδ1 hw χ hone z
  have hpoint := herr (allocatedRowIdealCoordinates B U b S rowSets z)
  rw [← hdensity] at hpoint
  have hproduct : (∏ s : Finset α, (χ (allocatedRowIdealCoordinates B U b S rowSets z s) : ℂ)) *
      ((volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width
        (allocatedLongJetRealCoordinates B U b S z) : ℂ)) =
      (volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width
        (allocatedLongJetRealCoordinates B U b S z) : ℂ) := by
    rw [mul_left_comm, hcutoff]
  rw [hproduct] at hpoint
  refine ⟨hpoint, ?_⟩
  have hvolume : 0 < volume := Finset.prod_pos (fun q _ => hR q.1.val.1)
  have hvolumeC : (volume : ℂ) ≠ 0 := by exact_mod_cast hvolume.ne'
  calc
    _ = ‖((volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width
          (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
        ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ := by
      congr 1
      field_simp [hvolumeC]
    _ = _ := by rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvolume]
    _ ≤ _ := div_le_div_of_nonneg_right hpoint hvolume.le

theorem exists_allocated_row_sliced_ideal_site_approximation (hR : ∀ j, 0 < R j)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (siteRadius : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hδp : (δ : ℝ)⁻¹ ≤ Real.exp p) :
    let radius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let C : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * radius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, jets a.1)) (Fintype.card α) p
    let volume : ℝ := ∏ q : (Σ a : {a // ¬grid a}, jets a.val.1), R q.1.val.1
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset α × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset α × LayerSamplerAxis I n → Fin k) → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + C) (f i s)) ∧
        (∀ i s v, (∃ d, 2 * (radius : ℝ) < |v d|) → f i s v = 0) ∧
        ∀ z : AllocatedLongJetRows B U b S jets,
          ‖(volume : ℂ) * (allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            ∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)‖ ≤ ε ∧
          ‖(allocatedRowSlicedIdeal B U b S rowSets δ center width (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
            (∑ i, a i * ∏ s, f i s (allocatedRowIdealCoordinates B U b S rowSets z s)) / (volume : ℂ)‖ ≤ ε / volume := by
  intro radius C Q volume
  obtain ⟨χ, hone, k, hk, hcard, a, f, ha, hf, hLf, hfsupport, herr⟩ :=
    exists_normalized_active_sliced_ideal_site_approximation (G := G) (Z := G × Option α) (B := B)
      (O := fun a : LayerSamplerAxis I n => jets a.1)
      hLayer grid (fun a => (Subtype.val : jets a.val.1 → Finset α)) center width δ hδ
      radius (allocatedRowSlicedSiteRadius_pos rowSets) hε hp hbox hεp hδp
  let alternateUniverse : Finset (Finset α × LayerSamplerAxis I n → Fin k) :=
    @Finset.univ _ (@Pi.instFintype (Finset α × LayerSamplerAxis I n) (fun _ => Fin k)
      (@instDecidableEqProd (Finset α) (LayerSamplerAxis I n) inferInstance
        (fun a b => Classical.propDecidable (a = b)))
      inferInstance (fun _ => Fin.fintype k))
  have huniv : (Finset.univ : Finset (Finset α × LayerSamplerAxis I n → Fin k)) =
      alternateUniverse := by
    ext i
    simp only [alternateUniverse, Finset.mem_univ]
  have hcard' : (Fintype.card (Finset α × LayerSamplerAxis I n → Fin k) : ℝ) ≤
      Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) := by
    simpa only [Q, Fintype.card_eq_nat_card] using hcard
  refine ⟨k, hk, hcard', a, f, ?_, hf, ?_, hfsupport, ?_⟩
  · calc
      (∑ i, ‖a i‖) = alternateUniverse.sum (fun i => ‖a i‖) := by rw [huniv]
      _ ≤ _ := ha
  · simpa only [Q] using hLf
  · intro z
    refine allocatedRowSlicedIdealApproximation_error B U b S rowSets center width hR δ hδ hδ1 hw χ hone a f ε ?_ z
    intro v
    rw [huniv]
    exact herr v

end Erdos3.VectorPolynomial

end

end OAI
