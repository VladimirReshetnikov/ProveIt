/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Dynamics.PositiveModerateBudget
import OAI.Combinatorics.Progressions.Fourier.AffineShortCoefficientMajorArc

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mem_rationalGridMajorBox {J : Type*} [Fintype J] [DecidableEq J]
    {M Q H : ℕ} (hM : 0 < M) (k : J → Fin M)
    {D : ℕ} (hD : 0 < D) (hDQ : D ≤ Q) (a : J → ℤ) {E : ℝ}
    (hclose : ∀ j, |((k j).val : ℝ) / M - (a j : ℝ) / D| ≤ E)
    (hE : M * E ≤ H) : k ∈ rationalGridMajorBox J M Q H := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact mem_rationalGridMajorSet hM hD hDQ (k j) (a j)
    (scaled_grid_approximation hM (k j) (a j) (D) (hclose j) hE)

theorem grid_large_spectrum_card {J : Type*} [Fintype J] [DecidableEq J]
    {M Q H : ℕ} (hM : 0 < M) (f : (J → Fin M) → ℂ) (ζ E : ℝ)
    (hmajor : ∀ k, ζ ≤ ‖f k‖ → ∃ D : ℕ, 0 < D ∧ D ≤ Q ∧
      ∃ a : J → ℤ, ∀ j, |((k j).val : ℝ) / M - (a j : ℝ) / D| ≤ E)
    (hE : M * E ≤ H) :
    ((Finset.univ.filter (fun k => ζ ≤ ‖f k‖)).card : ℝ) ≤
      ((Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1)) ^ Fintype.card J := by
  classical
  have hsub : Finset.univ.filter (fun k => ζ ≤ ‖f k‖) ⊆ rationalGridMajorBox J M Q H := by
    intro k hk
    obtain ⟨D, hD, hDQ, a, ha⟩ := hmajor k (Finset.mem_filter.mp hk).2
    exact mem_rationalGridMajorBox hM k hD hDQ a ha hE
  have hc : ((Finset.univ.filter (fun k => ζ ≤ ‖f k‖)).card : ℝ) ≤
      (rationalGridMajorBox J M Q H).card := by exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (rationalGridMajorBox_card J M Q H)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

theorem polynomial_weightedModerateBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : localizedMajorArcLengthBudget n U ζ ≤ c.length)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (shift : ℝ) (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hbias : ζ ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
        (fun x => character (((shift + (z none : ℝ)) *
          booleanBlockPhase ξ (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (localizedMajorArcBudget n U ζ * ((c.modulus none : ℝ) * U ^ n)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ /
          (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) := by
  let d j := (s j).majorArcLocalizationData A hA (h j) hζ hζ1 (hlen j)
  let e := c.majorArcLocalizationData A hA hc hζ hζ1 hclen
  let τ : Fin (n + 2) → ℝ := fun i => localizationThreshold U ζ i.val
  have hτ (j : Fin (n + 1)) : 0 < τ j.succ := localizationThreshold_pos hc.one_le hζ _
  have he : e.error (τ 1) ≤ τ 0 := by
    simpa only [τ, Fin.val_one, Fin.val_zero] using
      c.majorArcLocalizationData_error A hA hc hζ hζ1 hclen (i := 0) (by omega)
  have hd (j : Fin n) : (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ :=
    (s j).majorArcLocalizationData_error A hA (h j) hζ hζ1 (hlen j) (by omega)
  have hR (j : Fin n) (i : Option I) : ((d j).modulus i : ℝ) ≤ U :=
    (by exact_mod_cast (s j).modulus_le i : ((s j).modulus i : ℝ) ≤ (s j).modulusBound).trans
      (h j).modulus_le
  have hN (j : Fin n) : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength :=
    (s j).majorArcLocalizationData_cellLength A hA (h j) hζ hζ1 (hlen j)
  have hM : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ e.cellLength :=
    c.majorArcLocalizationData_cellLength A hA hc hζ hζ1 hclen
  have hb : τ 0 ≤ ‖e.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => character (((shift + (z none : ℝ)) *
          booleanBlockPhase ξ (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle)))‖ := by
    change localizationThreshold U ζ 0 ≤ _
    rw [localizationThreshold_zero]
    exact hbias
  obtain ⟨D, hD, hDb, a, ha⟩ := weightedModerateBlock_major_arc e d τ hτ he hd shift ξ J hJ hR hN hM hb
  refine ⟨D, hD, hDb, a, fun S => (ha S).trans ?_⟩
  have hcloss := c.majorArcLocalizationData_lengthLoss A hA hc hζ hζ1 hclen
  have hsloss j := (s j).majorArcLocalizationData_lengthLoss A hA (h j) hζ hζ1 (hlen j)
  apply coefficient_inverse_product_le (fun j => ((s j).length : ℝ))
    (fun j => ((d j).cellLength : ℝ))
    (by exact_mod_cast c.length_pos) (by exact_mod_cast e.cellLength_pos)
    (by exact_mod_cast c.modulus_pos none)
    (fun j => by exact_mod_cast (s j).length_pos)
    (fun j => by exact_mod_cast (d j).cellLength_pos)
    (e.length_le_lengthLoss_mul_cellLength.trans
      (mul_le_mul_of_nonneg_right hcloss (Nat.cast_nonneg _)))
    (fun j => (d j).length_le_lengthLoss_mul_cellLength.trans
      (mul_le_mul_of_nonneg_right (hsloss j) (Nat.cast_nonneg _)))
    (localizedMajorArcBudget_pos n hc.one_le hζ).le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

noncomputable def gridJetFrequency {I : Type*} [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (S : Finset I) : ℝ :=
  if h : S ∈ J then ((k ⟨S, h⟩).val : ℝ) / M else 0

theorem gridJetFrequency_apply {I : Type*} [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (S : J) :
    gridJetFrequency M J k S = ((k S).val : ℝ) / M := by
  simp only [gridJetFrequency, dite_eq_left S.property]

noncomputable def weightedCubeGridCoefficient {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I) (M : ℕ) (J : Finset (Finset I))
    (k : J → Fin M) : ℂ :=
  (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
    (fun z => character ((booleanBlockPhase (gridJetFrequency M J k)
      (fun j i => (z j i : ℝ)) : ℝ) : CircleFourier.Circle))

theorem weightedCubeGridCoefficient_mem_major {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    {M Q H : ℕ} (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hQ : (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card ≤ Q)
    (hH : M * (localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ)) ≤ H)
    (k : J → Fin M) (hk : ζ ≤ ‖weightedCubeGridCoefficient s M J k‖) :
    k ∈ rationalGridMajorBox J M Q H := by
  obtain ⟨D, hD, hDQ, a, ha⟩ := polynomial_weightedCubeBlock_major_arc s A hA h hζ hζ1 hlen
    (gridJetFrequency M J k) J hJ hk
  apply mem_rationalGridMajorBox hM k hD (by exact_mod_cast hDQ.trans hQ) a _ hH
  intro S
  simpa only [gridJetFrequency_apply] using ha S

theorem weightedCubeGridCoefficient_large_card {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    {M Q H : ℕ} (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hQ : (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card ≤ Q)
    (hH : M * (localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ)) ≤ H) :
    ((Finset.univ.filter (fun k => ζ ≤ ‖weightedCubeGridCoefficient s M J k‖)).card : ℝ) ≤
      ((Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1)) ^ J.card := by
  have hsub : Finset.univ.filter (fun k => ζ ≤ ‖weightedCubeGridCoefficient s M J k‖) ⊆
      rationalGridMajorBox J M Q H := by
    intro k hk
    exact weightedCubeGridCoefficient_mem_major s A hA h hζ hζ1 hlen hM J hJ hQ hH k
      (Finset.mem_filter.mp hk).2
  have hc : ((Finset.univ.filter (fun k => ζ ≤ ‖weightedCubeGridCoefficient s M J k‖)).card : ℝ) ≤
      (rationalGridMajorBox J M Q H).card := by exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (by
    simpa only [Fintype.card_coe] using rationalGridMajorBox_card J M Q H)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

noncomputable def weightedAffineModerateGridCoefficient {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (shift : ℝ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) : ℂ :=
  c.source.complexMean (fun z =>
    (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character (((shift + (z none : ℝ)) * booleanBlockPhase (gridJetFrequency M J k)
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))

theorem weightedAffineModerateGridCoefficient_mem_major {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : localizedMajorArcLengthBudget n U ζ ≤ c.length)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (shift : ℝ) {M Q H : ℕ} (hM : 0 < M)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hQ : (localizedMajorArcBudget n U ζ * ((c.modulus none : ℝ) * U ^ n)) ^ J.card ≤ Q)
    (hH : M * (localizedMajorArcErrorBudget n U ζ /
      (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ))) ≤ H)
    (k : J → Fin M) (hk : ζ ≤ ‖weightedAffineModerateGridCoefficient c s u v shift M J k‖) :
    k ∈ rationalGridMajorBox J M Q H := by
  obtain ⟨D, hD, hDQ, a, ha⟩ := polynomial_affine_weightedModerateBlock_major_arc c s A hA hc h hζ hζ1
    hclen hlen shift 1 Nat.zero_lt_one u v hv hstride (gridJetFrequency M J k) J hJ (by
      simpa only [weightedAffineModerateGridCoefficient, Nat.cast_one, one_mul] using hk)
  simp only [one_mul] at hDQ ha
  apply mem_rationalGridMajorBox hM k hD (by exact_mod_cast hDQ.trans hQ) a _ hH
  intro S
  simpa only [gridJetFrequency_apply, one_mul] using ha S

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

theorem weightedCubeGrid_sum_coefficient {B : Type*} [Fintype B] [DecidableEq B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (shift : CircleFourier.Circle) :
    (FiniteProbabilityWeights.pi (fun b =>
      FiniteProbabilityWeights.pi (fun j => (s b j).source))).complexMean
        (fun z => character (shift + ∑ b,
          ((booleanBlockPhase (gridJetFrequency M J k) (fun j i => (z b j i : ℝ)) : ℝ) :
            CircleFourier.Circle))) =
      character shift * ∏ b, weightedCubeGridCoefficient (s b) M J k :=
  independent_phase_coefficient
    (fun b => FiniteProbabilityWeights.pi (fun j => (s b j).source))
    (fun _b z => ((booleanBlockPhase (gridJetFrequency M J k) (fun j i => (z j i : ℝ)) : ℝ) :
      CircleFourier.Circle)) shift

theorem weightedCubeGridProduct_truncation_le {B : Type*} [Fintype B]
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U : ℝ}
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (ζ : ℕ → ℝ) (m : ℕ) (hζ : ∀ i ≤ m, 0 < ζ i ∧ ζ i ≤ 1)
    (hlen : ∀ i ≤ m, ∀ b j, localizedMajorArcLengthBudget n U (ζ i) ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (Q H : ℕ → ℕ)
    (hQ : ∀ i ≤ m, (localizedMajorArcBudget n U (ζ i) * U ^ (n + 1)) ^ J.card ≤ Q i)
    (hH : ∀ i ≤ m, ∀ b, M * (localizedMajorArcErrorBudget n U (ζ i) /
      ∏ j, ((s b j).length : ℝ)) ≤ H i)
    (ψ : (J → Fin M) → ℂ) (hψ : ∀ k, ‖ψ k‖ ≤ 1) :
    ‖(∑ k, (∏ b, weightedCubeGridCoefficient (s b) M J k) * ψ k) -
        ∑ k ∈ rationalGridMajorBox J M (Q 0) (H 0),
          (∏ b, weightedCubeGridCoefficient (s b) M J k) * ψ k‖ ≤
      (∑ i ∈ Finset.range m,
        (((Q (i + 1) + 1 : ℝ) * (2 * Q (i + 1) * (H (i + 1) + 1) + 1) *
          (2 * H (i + 1) + 1)) ^ J.card) * (ζ i) ^ Fintype.card B) +
        (M : ℝ) ^ J.card * (ζ m) ^ Fintype.card B := by
  let S i := rationalGridMajorBox J M (Q i) (H i)
  have hsmall : ∀ i ≤ m, ∀ b k, k ∉ S i →
      ‖weightedCubeGridCoefficient (s b) M J k‖ ≤ ζ i := by
    intro i hi b k hk
    by_contra hnot
    exact hk (weightedCubeGridCoefficient_mem_major (s b) A hA (h b)
      (hζ i hi).1 (hζ i hi).2 (hlen i hi b) hM J hJ (hQ i hi) (hH i hi b) k
      (le_of_lt (lt_of_not_ge hnot)))
  have ht := product_spectrum_truncation_levels
    (fun b k => weightedCubeGridCoefficient (s b) M J k) ψ hψ S ζ m
      (fun i hi => (hζ i hi).1.le) hsmall
  apply ht.trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right
    · simpa only [Fintype.card_coe] using rationalGridMajorBox_card J M (Q (i + 1)) (H (i + 1))
    · exact pow_nonneg (hζ i (by have := Finset.mem_range.mp hi; omega)).1.le _
  · exact le_of_eq (by simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

noncomputable def weightedModerateGridCoefficient {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (shift : ℝ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) : ℂ :=
  c.source.complexMean (fun z =>
    (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character (((shift + (z none : ℝ)) * booleanBlockPhase (gridJetFrequency M J k)
        (fun j i => (x j i : ℝ)) : ℝ) : CircleFourier.Circle)))

theorem weightedModerateGridCoefficient_mem_major {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : localizedMajorArcLengthBudget n U ζ ≤ c.length)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (shift : ℝ) {M Q H : ℕ} (hM : 0 < M)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hQ : (localizedMajorArcBudget n U ζ * ((c.modulus none : ℝ) * U ^ n)) ^ J.card ≤ Q)
    (hH : M * (localizedMajorArcErrorBudget n U ζ /
      (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ))) ≤ H)
    (k : J → Fin M) (hk : ζ ≤ ‖weightedModerateGridCoefficient c s shift M J k‖) :
    k ∈ rationalGridMajorBox J M Q H := by
  obtain ⟨D, hD, hDQ, a, ha⟩ := polynomial_weightedModerateBlock_major_arc c s A hA hc h hζ hζ1
    hclen hlen shift (gridJetFrequency M J k) J hJ hk
  apply mem_rationalGridMajorBox hM k hD (by exact_mod_cast hDQ.trans hQ) a _ hH
  intro S
  simpa only [gridJetFrequency_apply] using ha S

theorem weightedModerateGridCoefficient_large_card {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : localizedMajorArcLengthBudget n U ζ ≤ c.length)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (shift : ℝ) {M Q H : ℕ} (hM : 0 < M)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hQ : (localizedMajorArcBudget n U ζ * ((c.modulus none : ℝ) * U ^ n)) ^ J.card ≤ Q)
    (hH : M * (localizedMajorArcErrorBudget n U ζ /
      (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ))) ≤ H) :
    ((Finset.univ.filter (fun k => ζ ≤ ‖weightedModerateGridCoefficient c s shift M J k‖)).card : ℝ) ≤
      ((Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1)) ^ J.card := by
  have hsub : Finset.univ.filter (fun k => ζ ≤ ‖weightedModerateGridCoefficient c s shift M J k‖) ⊆
      rationalGridMajorBox J M Q H := by
    intro k hk
    exact weightedModerateGridCoefficient_mem_major c s A hA hc h hζ hζ1 hclen hlen shift
      hM J hJ hQ hH k (Finset.mem_filter.mp hk).2
  have hcard : ((Finset.univ.filter
      (fun k => ζ ≤ ‖weightedModerateGridCoefficient c s shift M J k‖)).card : ℝ) ≤
      (rationalGridMajorBox J M Q H).card := by exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (by simpa only [Fintype.card_coe] using rationalGridMajorBox_card J M Q H)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedPositiveAffineModerateGridCoefficient_mem_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : NormalizedScalarCubeSource Empty)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n ≤
      (s j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : ζ ≤ ‖weightedAffineModerateGridCoefficient c s u v 0 M J k‖) :
    k ∈ polynomialGridCover J M (positiveModerateCoverConstant n J.card U V)
      (positiveModerateCoverExponent n J.card) ζ := by
  have hU := hc.one_le
  have hU0 : 0 ≤ U := (by norm_num : (0 : ℝ) ≤ 1).trans hU
  have hLc : 0 < (c.length : ℝ) := Nat.cast_pos.mpr c.length_pos
  have hP : 0 < ∏ j, ((s j).length : ℝ) :=
    Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (s j).length_pos)
  have hlength := positiveModerateLengthBudget_bounds n hU hζ hζ1
  have hcover := positiveModerateCoverBudget_bounds n J.card hU hV hζ hζ1
  by_cases hlong : majorArcLengthConstant (n + 1) U / ζ ^ majorArcLengthExponent (n + 1) ≤
      (c.length : ℝ)
  · have hm : (c.modulus none : ℝ) ≤ U :=
      (by exact_mod_cast c.modulus_le none : (c.modulus none : ℝ) ≤ c.modulusBound).trans
        hc.modulus_le
    have hm1 : (1 : ℝ) ≤ c.modulus none := by exact_mod_cast c.modulus_pos none
    have hden : (c.length : ℝ) * ∏ j, ((s j).length : ℝ) ≤
        ((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 hLc.le) hP.le
    have hscale' : (M : ℝ) /
        (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) ≤ V :=
      (div_le_div_of_nonneg_left (Nat.cast_nonneg M) (mul_pos hLc hP) hden).trans hscale
    have hq := (localizedMajorArcBudget_pos (n + 1) hU hζ).le
    have hd : (localizedMajorArcBudget (n + 1) U ζ *
        ((c.modulus none : ℝ) * U ^ (n + 1))) ^ J.card ≤
        (localizedMajorArcBudget (n + 1) U ζ * U ^ (n + 1 + 1)) ^ J.card := by
      apply pow_le_pow_left₀ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hq
      rw [pow_succ' U (n + 1)]
      exact mul_le_mul_of_nonneg_right hm (pow_nonneg hU0 _)
    apply weightedAffineModerateGridCoefficient_mem_major c s A hA hc h hζ hζ1
      ((localizedMajorArcLengthBudget_le_power (n + 1) hU hζ hζ1).trans hlong)
      (fun j => (localizedMajorArcLengthBudget_le_power (n + 1) hU hζ hζ1).trans
        (hlength.2.trans (hlen j))) u v hv hstride 0 hM J hJ
    · exact (hd.trans (majorArc_denominator_le_cover (n + 1) J.card hU hV hζ hζ1)).trans
        (hcover.2.1.trans (Nat.le_ceil _))
    · exact (majorArc_scaled_error_le_cover (n + 1) J.card hU hV hζ hζ1 hscale').trans
        (hcover.2.1.trans (Nat.le_ceil _))
    · exact hk
  · have hV4 : 0 ≤ 4 * V := by positivity
    have hbias : ζ ≤ ‖c.source.complexMean (fun z =>
        (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
          (fun x => CircleFourier.character (((z none : ℝ) *
            booleanBlockPhase (gridJetFrequency M J k) (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) :
              CircleFourier.Circle)))‖ := by
      simpa only [weightedAffineModerateGridCoefficient, zero_add] using hk
    obtain ⟨D, hD, hDb, a, ha⟩ := affine_weighted_positiveCoefficient_major_arc (T := (c.length : ℝ)) c.source
      (fun z => (z none : ℤ)) s A hA h hζ hζ1 (show 0 < (c.length : ℝ) / 4 by positivity)
      (fun z hz => ⟨hpositive z hz, by
        exact_mod_cast (Finset.mem_Ico.mp (z none).property).2.le⟩)
      (fun j => (localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans
        (hlength.1.trans (hlen j))) u v hv hstride (gridJetFrequency M J k) J hJ hbias
    have hraw : 0 ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card := by
      have := (localizedMajorArcBudget_pos n hU hζ).le
      positivity
    have hupper : 0 ≤ majorArcLengthConstant (n + 1) U /
        ζ ^ majorArcLengthExponent (n + 1) := by
      have := (majorArcLengthConstant_pos (n + 1) hU).le
      positivity
    have hDQ : (D : ℝ) ≤ positiveModerateCoverConstant n J.card U V /
        ζ ^ positiveModerateCoverExponent n J.card := hDb.trans
      ((mul_le_mul (lt_of_not_ge hlong).le
        (majorArc_denominator_le_cover n J.card hU hV4 hζ hζ1) hraw hupper).trans
          hcover.2.2)
    have hscale' : (M : ℝ) / (((c.length : ℝ) / 4) * ∏ j, ((s j).length : ℝ)) ≤
        4 * V := by
      calc
        _ = 4 * ((M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by norm_num)
    apply mem_rationalGridMajorBox hM k hD
      (by exact_mod_cast hDQ.trans (Nat.le_ceil _)) a
      (fun S => by simpa only [gridJetFrequency_apply] using ha S)
    exact (majorArc_scaled_error_le_cover n J.card hU hV4 hζ hζ1 hscale').trans
      (hcover.1.trans (Nat.le_ceil _))

theorem weightedPositiveAffineModerateGridCoefficient_minor_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : NormalizedScalarCubeSource Empty)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n ≤
      (s j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : k ∉ polynomialGridCover J M (positiveModerateCoverConstant n J.card U V)
      (positiveModerateCoverExponent n J.card) ζ) :
    ‖weightedAffineModerateGridCoefficient c s u v 0 M J k‖ ≤ ζ := by
  exact le_of_lt (lt_of_not_ge (fun hh => hk
    (weightedPositiveAffineModerateGridCoefficient_mem_polynomial c s A hA hc h u v hv hstride hpositive
      hV hζ hζ1 hlen hM hscale J hJ k hh)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem weightedCubeGridCoefficient_norm_le_one {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    ‖weightedCubeGridCoefficient s M J k‖ ≤ 1 := by
  let p := FiniteProbabilityWeights.pi (fun j => (s j).source)
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by
    simp only [norm_character, p.mean_const])

theorem weightedModerateGridCoefficient_norm_le_one {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (shift : ℝ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    ‖weightedModerateGridCoefficient c s shift M J k‖ ≤ 1 := by
  let p := FiniteProbabilityWeights.pi (fun j => (s j).source)
  apply (c.source.norm_complexMean_le_mean_norm _).trans
  apply (c.source.mean_mono (fun z => ?_)).trans_eq (c.source.mean_const 1)
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by
    simp only [norm_character, p.mean_const])

theorem sum_eq_retained_add_spectrumTail {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (f : K → ℝ) : ∑ k, f k = (∑ k ∈ S, f k) + spectrumTail S f := by
  calc
    _ = ∑ k, ((if k ∈ S then f k else 0) + (if k ∈ S then 0 else f k)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false, add_zero, zero_add]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, spectrumTail]

theorem product_spectrum_absolute_cap {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : Finset K) (hunit : ∀ b k, ‖c b k‖ ≤ 1) :
    (∑ k, ‖∏ b, c b k‖) ≤ S.card + spectrumTail S (fun k => ‖∏ b, c b k‖) := by
  rw [sum_eq_retained_add_spectrumTail S]
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ ∑ _k ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [one_pow] using norm_product_coefficients_le (fun b => c b k) (fun b => hunit b k)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def uniformSpectrumAbsoluteCap (n j t : ℕ) (U V W : ℝ) : ℝ :=
  uniformSpectrumSizeConstant n j t U V W + 1

theorem uniformBlockSpectrum_absolute_cap {B J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hB : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hunit : ∀ b k, ‖coeff b k‖ ≤ 1)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖coeff b k‖ ≤ δ) :
    (∑ k, ‖∏ b, coeff b k‖) ≤ uniformSpectrumAbsoluteCap n (Fintype.card J) t U V W := by
  classical
  obtain ⟨hζ, hζ1, hacc⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW (by norm_num : (0 : ℝ) < 1)
  let S := uniformBlockSpectrumCover J M n U V L (uniformBlockRetainedBias n (Fintype.card J) t U V W 1)
  have ht := uniformBlockSpectrum_tail M n t coeff hU hV hW hL hζ hζ1 (by norm_num) hB hsize hminor hacc
  have hc : (S.card : ℝ) ≤ uniformSpectrumSizeConstant n (Fintype.card J) t U V W := by
    simpa only [one_pow, div_one] using uniformBlockSpectrumCover_polynomial_card J M n t
      hU hV hW hL (by norm_num : (0 : ℝ) < 1) le_rfl hsize
  exact (product_spectrum_absolute_cap coeff S hunit).trans (add_le_add hc ht)

theorem finite_product_retained_mass_le {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (coeff : B → K → ℂ) (S : Finset K) {A : ℝ} (hcap : (∑ k, ‖∏ b, coeff b k‖) ≤ A) :
    (∑ k ∈ S, ‖∏ b, coeff b k‖) ≤ A := by
  apply le_trans _ hcap
  exact Finset.sum_le_univ_sum_of_nonneg (fun _ => norm_nonneg _)

end Erdos3

end

end OAI
