import OAI.Combinatorics.Progressions.Estimates.ReindexedCubeDomain

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem exists_cube_minor_probability_bound {O α : Type*}
    [Fintype O] [Fintype α] [DecidableEq O] [DecidableEq α]
    (c : O → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c o|) :
    ∃ r : O → Option α, ∀ d : ℕ, 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ u : ℝ, 0 < u →
      (blockCubeMeasure O (Fin h) α).real
        {a | |booleanMinorDeterminant c sets id (⟨0, hh⟩ : Fin h) r a| ≤ u} ≤
        scalarCubeDomainDensity α ^ Fintype.card (O × Fin h) * multivariateSublevelConstant N d *
          (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨r, hr⟩ := exists_boolean_minor_sublevel_bound c sets hsets h hh hcard e hN hc₀ hc
  refine ⟨r, ?_⟩
  intro d hd hdeg u hu
  have hsm : MeasurableSet {a | |booleanMinorDeterminant c sets id (⟨0, hh⟩ : Fin h) r a| ≤ u} :=
    measurableSet_le (booleanMinorDeterminant_contDiff c sets id (⟨0, hh⟩ : Fin h) r).continuous.measurable.abs
      measurable_const
  rw [blockCubeMeasure_real_reindex e _ hsm]
  have hvol := hr d hd hdeg (reindexedBlockCubeDomain e) 1 u le_rfl
    (fun x hx j => reindexedBlockCubeDomain_box e hx j) hu
  simp only [one_pow, one_mul] at hvol
  have hmul := mul_le_mul_of_nonneg_left hvol
    (pow_nonneg (scalarCubeDomainDensity_pos α).le (Fintype.card (O × Fin h)))
  exact hmul.trans_eq (by ring)

theorem exists_allocated_cube_minor_probability_bound {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (hsets : Function.Injective sets)
    (h : ℕ) (hh : 0 < h) (hcard : ∀ o, (sets o).card ≤ h)
    (block : O → B) (hblock : Function.Injective block)
    {N : ℕ} (e : BlockParameter O (Fin h) α ≃ Fin N) (hN : 0 < N)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (hc : ∀ o, c₀ ≤ |c (block o)|) :
    ∃ r : O → Option α, ∀ d : ℕ, 0 < d → Fintype.card O * (h - 1) ≤ d →
      ∀ u : ℝ, 0 < u →
      (blockCubeMeasure B (Fin h) α).real
        {a | |booleanMinorDeterminant c sets block (⟨0, hh⟩ : Fin h) r a| ≤ u} ≤
        scalarCubeDomainDensity α ^ Fintype.card (O × Fin h) * multivariateSublevelConstant N d *
          (u * (d + 1 : ℝ) ^ N / c₀ ^ Fintype.card O) ^ (((N * d : ℕ) : ℝ)⁻¹) := by
  obtain ⟨r, hr⟩ := exists_cube_minor_probability_bound (c ∘ block) sets hsets h hh hcard e hN hc₀ hc
  refine ⟨r, ?_⟩
  intro d hd hdeg u hu
  rw [booleanMinorDeterminant_sublevel_marginal c sets block hblock]
  exact hr d hd hdeg u hu

end Erdos3

end

end OAI
