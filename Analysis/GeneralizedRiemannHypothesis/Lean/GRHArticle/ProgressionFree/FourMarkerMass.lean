import GRHArticle.ProgressionFree.ExactRuleApproximation
import GRHArticle.ProgressionFree.FourMarkerExchange
import GRHArticle.ProgressionFree.SatelliteProfiles

/-!
# Reciprocal mass of the four-marker construction

At each cutoff containing all insertions, the added mass is exact and the
deleted mass admits the article's upper bound. The formulas retain the
common all-ones satellite factor.
-/

open scoped BigOperators

namespace GRHArticle.ProgressionFree

private theorem fourMarker_mem_bounds {k : ℕ} (hk : k ∈ fourMarkerExponents) :
    k ≤ 14 ∧ k % 3 = 2 := by
  simp only [fourMarkerExponents, Finset.mem_insert, Finset.mem_singleton] at hk
  omega

private theorem sum_exactPatternWeight_product {ι : Type*} [Fintype ι]
    (A : Finset ℕ) (T : Finset (ι → ℕ)) (w : ℝ) (u : ι → ℝ) :
    (∑ v ∈ A ×ˢ T, exactPatternWeight w u v) =
      (∑ a ∈ A, w ^ a) * ∑ v ∈ T, ∏ i, u i ^ v i := by
  rw [Finset.sum_product]
  simp only [exactPatternWeight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem inserted_iff_product_profiles {ι : Type*} [Fintype ι] (v : ℕ × (ι → ℕ)) :
    fourMarkerInserted v ↔ v ∈ fourMarkerExponents ×ˢ
      ((({(fun _ : ι => (1 : ℕ))} : Finset (ι → ℕ)) ∪ raisedSatelliteProfiles 2) ∪
        raisedSatelliteProfiles 4) := by
  classical
  simp only [fourMarkerInserted, Finset.mem_product, Finset.mem_union, Finset.mem_singleton,
    mem_raisedSatelliteProfiles_iff]
  constructor
  · rintro ⟨hk, h | ⟨q, hq, h₂ | h₄⟩⟩
    · exact ⟨hk, Or.inl (Or.inl (funext h))⟩
    · exact ⟨hk, Or.inl (Or.inr ⟨q, hq, h₂⟩)⟩
    · exact ⟨hk, Or.inr ⟨q, hq, h₄⟩⟩
  · rintro ⟨hk, (h | ⟨q, hq, h₂⟩) | ⟨q, hq, h₄⟩⟩
    · exact ⟨hk, Or.inl (congrFun h)⟩
    · exact ⟨hk, Or.inr ⟨q, hq, Or.inl h₂⟩⟩
    · exact ⟨hk, Or.inr ⟨q, hq, Or.inr h₄⟩⟩

private theorem bounded_inserted_eq {ι : Type*} [Fintype ι] {L : ℕ} (hL : 14 < L) :
    boundedExactPatterns {v : ℕ × (ι → ℕ) | fourMarkerInserted v} L = fourMarkerExponents ×ˢ
      ((({(fun _ : ι => (1 : ℕ))} : Finset (ι → ℕ)) ∪ raisedSatelliteProfiles 2) ∪
        raisedSatelliteProfiles 4) := by
  classical
  ext v
  rw [mem_boundedExactPatterns, ← inserted_iff_product_profiles]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, (fourMarker_mem_bounds h.1).1.trans_lt hL, ?_⟩
    intro q
    rcases h.2 with hall | ⟨i, hrest, hi⟩
    · rw [hall q]
      omega
    · by_cases hqi : q = i
      · subst q
        rcases hi with h₂ | h₄ <;> omega
      · rw [hrest q hqi]
        omega

private theorem sum_insertedProfiles {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    (∑ v ∈ ((({(fun _ : ι => (1 : ℕ))} : Finset (ι → ℕ)) ∪ raisedSatelliteProfiles 2) ∪
        raisedSatelliteProfiles 4), ∏ i, u i ^ v i) =
      (∏ i, u i) * (1 + (∑ i, u i) + ∑ i, u i ^ 3) := by
  classical
  have h₂₁ := disjoint_raisedSatelliteProfiles_allOnes (ι := ι) (e := 2) (by decide)
  have h₄₁ := disjoint_raisedSatelliteProfiles_allOnes (ι := ι) (e := 4) (by decide)
  have h₂₄ := disjoint_raisedSatelliteProfiles_of_ne (ι := ι) (e := 2) (e' := 4)
    (by decide) (by decide)
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨h₄₁.symm, h₂₄⟩),
    Finset.sum_union h₂₁.symm, sum_raisedSatelliteProfiles_weight u (show 1 < 2 by decide),
    sum_raisedSatelliteProfiles_weight u (show 1 < 4 by decide)]
  simp only [Finset.sum_singleton, pow_one]
  norm_num
  ring

/-- The article's scaled reciprocal-mass lower bound, before replacing the
satellite weights by prime reciprocals. An arbitrary upper bound `U` on the
truncated greedy marker mass suffices. -/
theorem fourMarker_exactPatternMass_sub_ge {ι : Type*} [Fintype ι] (u : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) {L : ℕ} (hL : 14 < L) {U : ℝ}
    (hU : (∑ a ∈ greedyExponentsBelow L, (1 / (2 : ℝ)) ^ a) ≤ U) :
    let m := ∑ k ∈ fourMarkerExponents, (1 / (2 : ℝ)) ^ k
    let v := ∑ k ∈ fourMarkerExponents, (1 / (2 : ℝ)) ^ (2 * k)
    (∏ i, u i) * (m - (U - 1) + ∑ i, (m * u i - v * u i ^ 2 - (U - m) * u i ^ 3)) ≤
      exactPatternMass (1 / 2) u (fourMarkerExponentSet ι) L -
        exactPatternMass (1 / 2) u (rankinExactExponentSet ι) L := by
  classical
  intro m v
  let A := greedyExponentsBelow L
  let σ := ∑ a ∈ A, (1 / (2 : ℝ)) ^ a
  let P := ∏ i, u i
  let W := exactPatternWeight (1 / 2) u
  let D₀ := (A.erase 0) ×ˢ ({(fun _ : ι => (1 : ℕ))} : Finset (ι → ℕ))
  let D₄ := A ×ˢ (raisedSatelliteProfiles (ι := ι) 4)
  let D₃ := (fourMarkerExponents.image (fun k => 2 * k)) ×ˢ (raisedSatelliteProfiles (ι := ι) 3)
  let K := boundedExactPatterns {w : ℕ × (ι → ℕ) | fourMarkerKept w} L
  let D := boundedExactPatterns {w : ℕ × (ι → ℕ) |
    w ∈ rankinExactExponentSet ι ∧ fourMarkerDeleted w} L
  let I := boundedExactPatterns {w : ℕ × (ι → ℕ) | fourMarkerInserted w} L
  have hOld : boundedExactPatterns (rankinExactExponentSet ι) L = K ∪ D := by
    ext z
    simp only [K, D, Finset.mem_union, mem_boundedExactPatterns, Set.mem_setOf_eq,
      rankinExactExponentSet, fourMarkerKept]
    by_cases h : fourMarkerDeleted z <;> simp [h]
  have hNew : boundedExactPatterns (fourMarkerExponentSet ι) L = K ∪ I := by
    ext z
    simp only [K, I, Finset.mem_union, mem_boundedExactPatterns, Set.mem_setOf_eq,
      fourMarkerExponentSet]
    tauto
  have hDisjOld : Disjoint K D := by
    apply Finset.disjoint_left.mpr
    intro z hzK hzD
    exact (mem_boundedExactPatterns.mp hzK).1.2.2 (mem_boundedExactPatterns.mp hzD).1.2
  have hDisjNew : Disjoint K I := by
    apply Finset.disjoint_left.mpr
    intro z hzK hzI
    have hg := (mem_greedyExponents_iff z.1).mp (mem_boundedExactPatterns.mp hzK).1.1 |>.1
    have hm := (fourMarker_mem_bounds (mem_boundedExactPatterns.mp hzI).1.1).2
    omega
  have hdiff :
      exactPatternMass (1 / 2) u (fourMarkerExponentSet ι) L -
        exactPatternMass (1 / 2) u (rankinExactExponentSet ι) L =
        (∑ z ∈ I, W z) - ∑ z ∈ D, W z := by
    unfold exactPatternMass
    rw [hOld, hNew, Finset.sum_union hDisjOld, Finset.sum_union hDisjNew]
    ring
  have hI : (∑ z ∈ I, W z) = m * (P * (1 + (∑ i, u i) + ∑ i, u i ^ 3)) := by
    unfold I W
    rw [bounded_inserted_eq hL, sum_exactPatternWeight_product, sum_insertedProfiles]
  have hDsub : D ⊆ D₀ ∪ D₄ ∪ D₃ := by
    intro z hz
    obtain ⟨⟨hzA, hzD⟩, ha, _⟩ := mem_boundedExactPatterns.mp hz
    have hzA' : z.1 ∈ A := mem_greedyExponentsBelow.mpr ⟨hzA.1, ha⟩
    rcases hzD with ⟨hall, ha₀⟩ | ⟨q, hrest, h₄ | ⟨h₃, k, hk, he⟩⟩
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
        ⟨Finset.mem_erase.mpr ⟨ha₀.ne', hzA'⟩, Finset.mem_singleton.mpr (funext hall)⟩))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr
        ⟨hzA', mem_raisedSatelliteProfiles_iff.mpr ⟨q, hrest, h₄⟩⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨k, hk, he.symm⟩, mem_raisedSatelliteProfiles_iff.mpr ⟨q, hrest, h₃⟩⟩))
  have hD04 : Disjoint D₀ D₄ :=
    Finset.disjoint_product.mpr (Or.inr
      (disjoint_raisedSatelliteProfiles_allOnes (e := 4) (by decide)).symm)
  have hD03 : Disjoint D₀ D₃ :=
    Finset.disjoint_product.mpr (Or.inr
      (disjoint_raisedSatelliteProfiles_allOnes (e := 3) (by decide)).symm)
  have hD43 : Disjoint D₄ D₃ :=
    Finset.disjoint_product.mpr (Or.inr
      (disjoint_raisedSatelliteProfiles_of_ne (e := 4) (e' := 3) (by decide) (by decide)))
  have hzero : 0 ∈ A := mem_greedyExponentsBelow.mpr ⟨zero_mem_greedyExponents, by omega⟩
  have hD₀ : (∑ z ∈ D₀, W z) = (σ - 1) * P := by
    unfold D₀ W
    rw [sum_exactPatternWeight_product, Finset.sum_erase_eq_sub hzero]
    simp only [pow_zero, Finset.sum_singleton, pow_one, σ, P]
  have hD₄ : (∑ z ∈ D₄, W z) = σ * (P * ∑ i, u i ^ 3) := by
    unfold D₄ W
    rw [sum_exactPatternWeight_product, sum_raisedSatelliteProfiles_weight u (show 1 < 4 by decide)]
  have hD₃ : (∑ z ∈ D₃, W z) = v * (P * ∑ i, u i ^ 2) := by
    unfold D₃ W
    rw [sum_exactPatternWeight_product, sum_raisedSatelliteProfiles_weight u (show 1 < 3 by decide),
      Finset.sum_image (fun a _ b _ h => by omega)]
  have hDle : (∑ z ∈ D, W z) ≤ (σ - 1) * P + σ * (P * ∑ i, u i ^ 3) + v * (P * ∑ i, u i ^ 2) := by
    calc
      _ ≤ ∑ z ∈ D₀ ∪ D₄ ∪ D₃, W z :=
        Finset.sum_le_sum_of_subset_of_nonneg hDsub fun z _ _ =>
          mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => pow_nonneg (hu i) _)
      _ = _ := by
        rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hD03, hD43⟩),
          Finset.sum_union hD04, hD₀, hD₄, hD₃]
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => hu i
  have hsum3 : 0 ≤ ∑ i, u i ^ 3 := Finset.sum_nonneg fun i _ => pow_nonneg (hu i) _
  have h₀ := mul_le_mul_of_nonneg_right (sub_le_sub_right hU 1) hP
  have h₄ := mul_le_mul_of_nonneg_right hU (mul_nonneg hP hsum3)
  change (P * (m - (U - 1) + ∑ i, (m * u i - v * u i ^ 2 - (U - m) * u i ^ 3))) ≤ _
  calc
    _ = m * (P * (1 + (∑ i, u i) + ∑ i, u i ^ 3)) -
      ((U - 1) * P + U * (P * ∑ i, u i ^ 3) + v * (P * ∑ i, u i ^ 2)) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    _ ≤ _ := by
      rw [hdiff, hI]
      linarith only [hDle, h₀, h₄]

end GRHArticle.ProgressionFree
