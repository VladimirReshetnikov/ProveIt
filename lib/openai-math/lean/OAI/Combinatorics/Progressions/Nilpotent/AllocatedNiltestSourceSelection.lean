import OAI.Combinatorics.Progressions.Dynamics.SampledFullboxDetectionBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalCubeSelection
import OAI.Combinatorics.Progressions.Estimates.CommonStrideCorrelation
import OAI.Combinatorics.Progressions.Estimates.SourceDetectionError
import OAI.Combinatorics.Progressions.Geometry.SampledDenseCommonBox
import OAI.Combinatorics.Progressions.Polynomial.PolynomialBoxDetection

namespace OAI

universe u v w w₁ w₂ w₃ w₄

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_nested_box_niltest_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (p : ℝ), 0 ≤ p →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (T : D.Niltest (fun _ : I => 1)), T.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ (c b : I → ℤ) (m d : ℕ) (H K : I → ℕ), 0 < m → 0 < d → (∀ i, 0 < K i) →
      commonStrideBox b d K ⊆ commonStrideBox c m H →
      ∀ f : (I → ℤ) → ℂ, (∀ x ∈ commonStrideBox b d K, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ ‖finiteCorrelation (commonStrideBox b d K) f
        (fun y => T.eval (commonStrideIndex c m y))‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => f (commonStridePoint b d x)) := by
  obtain ⟨C, hC, hdetect⟩ := exists_polynomial_box_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ L _ _ dim _ _ _ _ D p hp hI T hT c b m d H K hm hd hK hsub f hf hcorr
  obtain ⟨U, hU, heval⟩ := T.exists_nested_box_restriction c b hm hd H K hK hsub
  let _ : ∀ i, NeZero (K i) := fun i => ⟨(hK i).ne'⟩
  have hzero : translatedIntegerBox (0 : I → ℤ) K = integerBox K := by
    simp [translatedIntegerBox, translateSupport]
  have hcorr' : Real.exp (-p) ≤ ‖finiteCorrelation (integerBox K)
      (fun x => f (commonStridePoint b d x)) U.eval‖ := by
    rw [finiteCorrelation_commonStrideBox b hd] at hcorr
    have he : finiteCorrelation (integerBox K) (fun x => f (commonStridePoint b d x)) U.eval =
        finiteCorrelation (integerBox K) (fun x => f (commonStridePoint b d x))
          (fun x => T.eval (commonStrideIndex c m (commonStridePoint b d x))) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [heval x hx]
    rwa [he]
  have hn := hdetect D p hp hI (fun _ : I => 1) (fun _ => zero_lt_one) U ((hU _).mpr hT)
    0 K (fun x => f (commonStridePoint b d x))
    (fun x hx => hf _ (commonStridePoint_mem b d K (hzero ▸ hx))) (hzero.symm ▸ hcorr')
  simpa only [hzero] using hn

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_finite_site_niltest_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I] {L : Type u} [LieRing L] [LieAlgebra ℚ L] {dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (p : ℝ), 0 ≤ p →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) p →
      ∀ (U : D.Niltest (fun _ : I => 1)), U.ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) p) →
      ∀ {T : Type w} [Nonempty T] [DecidableEq T] (e : T → I → ℤ), Function.Injective e →
      ∀ (A S : Finset T) (c b : I → ℤ) (m d : ℕ) (H K : I → ℕ),
      0 < m → 0 < d → (∀ i, 0 < K i) → A ⊆ S →
      S.image e = commonStrideBox c m H → A.image e = commonStrideBox b d K →
      ∀ (f w : T → ℂ), (∀ t, ‖f t‖ ≤ 1) →
      (∀ t ∈ S, w t = star (U.eval (commonStrideIndex c m (e t)))) →
      Real.exp (-p) ≤ ‖𝔼 t ∈ A, f t * w t‖ →
      Real.exp (-((p + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => finiteSiteExtension e f (commonStridePoint b d x)) := by
  obtain ⟨C, hC, hdetect⟩ := exists_nested_box_niltest_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ L _ _ dim _ _ _ _ D p hp hI U hU T _ _ e he A S c b m d H K hm hd hK hAS hS hA f w hf hw hc
  have hsub : commonStrideBox b d K ⊆ commonStrideBox c m H := by
    rw [← hA, ← hS]
    exact Finset.image_subset_image hAS
  have heq := finiteSiteExtension_test_mean e he A f w
    (fun y => U.eval (commonStrideIndex c m y)) (fun t ht => hw t (hAS ht))
  rw [heq, hA] at hc
  exact hdetect D p hp hI U hU c b m d H K hm hd hK hsub (finiteSiteExtension e f)
    (fun x _ => finiteSiteExtension_norm_le e f hf x) hc

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

theorem exists_sampled_niltest_cube_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I]
      {Ω : Type w₁} [Fintype Ω] [Nonempty Ω] {T : Type w₂} [Fintype T] [Nonempty T]
      {X : Type w₃} {J : Ω → Type w₄} [∀ z, Nonempty (J z)]
      {L : ∀ z, J z → Type u} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
      {dim : ∀ z, J z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)] [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
      (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dim z j))
      (U : ∀ z j, (D z j).Niltest (fun _ : I => 1))
      (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
      (S : ∀ z, J z → Finset T) (e : T → I → ℤ), Function.Injective e →
      ∀ (c : ∀ z, J z → I → ℤ) (m : ∀ z, J z → ℕ) (H : ∀ z, J z → I → ℕ),
      (∀ z j, 0 < m z j) → (∀ z j, (S z j).image e = commonStrideBox (c z j) (m z j) (H z j)) →
      ∀ (p q : ℝ) (N : I → ℕ), 0 ≤ p → 0 ≤ q →
      (∀ z j, IsDenseCommonStrideBox N p ((S z j).image e)) →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q →
      (∀ z j, (U z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q)) →
      (∀ z j, ((U z j).normBound : ℝ) ≤ 1) →
      ∀ (v : X → ℂ) (α : ℝ), (∀ x, ‖v x‖ ≤ 1) → 0 < α → α ≤ 1 →
      Fintype.card I * Real.exp (-p) ≤ α / 8 → Real.exp (-q) ≤ α / 4 →
      α ≤ sampledSliceSeminorm μ F S
        (fun z j t => star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))) v →
      ∃ (b : I → ℤ) (d : ℕ) (K : I → ℕ), 0 < d ∧ (∀ i, 0 < K i) ∧
        IsDenseCommonStrideBox N (p + 1) (commonStrideBox b d K) ∧
        commonStrideBox b d K ⊆ Finset.univ.image e ∧
        (Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) * (α / 2)) *
          Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) ≤
          (μ.complexMean (fun z => normalizedSupportedCubeSum (s + 1) (integerBox K)
            (fun _ x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x)))).re := by
  obtain ⟨C, hC, hdetect⟩ := exists_finite_site_niltest_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ Ω _ _ T _ _ X J _ L _ _ dim _ _ _ _ D U μ F S e he c m H hm hS p q N hp hq
    hslice hI hU hcap v α hv hα hαone hmesh hthreshold hmean
  let w : ∀ z, J z → T → ℂ := fun z j t =>
    star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))
  have hw (z) (j) (t) : ‖w z j t‖ ≤ 1 := by
    simpa only [w, norm_star] using
      ((U z j).norm_eval_le (commonStrideIndex (c z j) (m z j) (e t))).trans (hcap z j)
  obtain ⟨A, hAn, hAdense, G, j, hmass, hcorr⟩ :=
    exists_dense_common_sampled_box_of_seminorm μ F S w e he hp N hslice hw v hv hα hαone hmesh hmean
  have hDense := hAdense
  obtain ⟨b, d, K, hd, hK, _, _, hA⟩ := hAdense
  have hnorm (z : Ω) (hz : z ∈ G) :
      Real.exp (-((q + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x)) := by
    exact hdetect (D z (j z)) q hq hI (U z (j z)) (hU z (j z)) e he A (S z (j z))
      (c z (j z)) b (m z (j z)) d (H z (j z)) K (hm z (j z)) hd hK
      (hcorr z hz).1 (hS z (j z)) hA (fun t => v (F z t)) (w z (j z))
      (fun t => hv _) (fun _ _ => rfl) (hthreshold.trans (hcorr z hz).2)
  refine ⟨b, d, K, hd, hK, ?_, ?_, ?_⟩
  · rw [← hA]
    exact hDense
  · rw [← hA]
    exact Finset.image_subset_image (Finset.subset_univ A)
  · let _ : ∀ i, NeZero (K i) := fun i => ⟨(hK i).ne'⟩
    exact sampled_normalized_cube_lower_bound (boxReduction_reflectsPairSums K) μ G s
      (fun z x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x))
      (Real.exp_nonneg _) hmass hnorm

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

theorem exists_sampled_niltest_cube_detection_with_sides (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I]
      {Ω : Type w₁} [Fintype Ω] [Nonempty Ω] {T : Type w₂} [Fintype T] [Nonempty T]
      {X : Type w₃} {J : Ω → Type w₄} [∀ z, Nonempty (J z)]
      {L : ∀ z, J z → Type u} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
      {dim : ∀ z, J z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)] [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
      (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dim z j))
      (U : ∀ z j, (D z j).Niltest (fun _ : I => 1))
      (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
      (S : ∀ z, J z → Finset T) (e : T → I → ℤ), Function.Injective e →
      ∀ (c : ∀ z, J z → I → ℤ) (m : ∀ z, J z → ℕ) (H : ∀ z, J z → I → ℕ),
      (∀ z j, 0 < m z j) → (∀ z j, (S z j).image e = commonStrideBox (c z j) (m z j) (H z j)) →
      ∀ (p q : ℝ) (N : I → ℕ), 0 ≤ p → 0 ≤ q →
      (∀ z j, IsDenseCommonStrideBox N p ((S z j).image e)) →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q →
      (∀ z j, (U z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q)) →
      (∀ z j, ((U z j).normBound : ℝ) ≤ 1) →
      ∀ (v : X → ℂ) (α : ℝ), (∀ x, ‖v x‖ ≤ 1) → 0 < α → α ≤ 1 →
      Fintype.card I * Real.exp (-p) ≤ α / 8 → Real.exp (-q) ≤ α / 4 →
      α ≤ sampledSliceSeminorm μ F S
        (fun z j t => star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))) v →
      ∃ (b : I → ℤ) (d : ℕ) (K : I → ℕ), 0 < d ∧ (∀ i, 0 < K i) ∧
        (∀ i, integerProgressionSupport (b i) (d : ℤ) (K i) ⊆ Finset.Ico (0 : ℤ) (N i : ℤ)) ∧
        (∀ i, Real.exp (-(p + 1)) * N i ≤ (K i : ℝ)) ∧
        IsDenseCommonStrideBox N (p + 1) (commonStrideBox b d K) ∧
        commonStrideBox b d K ⊆ Finset.univ.image e ∧
        (Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) * (α / 2)) *
          Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) ≤
          (μ.complexMean (fun z => normalizedSupportedCubeSum (s + 1) (integerBox K)
            (fun _ x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x)))).re := by
  obtain ⟨C, hC, hdetect⟩ := exists_finite_site_niltest_detection s P
  refine ⟨C, hC, ?_⟩
  intro I _ _ Ω _ _ T _ _ X J _ L _ _ dim _ _ _ _ D U μ F S e he c m H hm hS p q N hp hq
    hslice hI hU hcap v α hv hα hαone hmesh hthreshold hmean
  let w : ∀ z, J z → T → ℂ := fun z j t =>
    star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))
  have hw (z) (j) (t) : ‖w z j t‖ ≤ 1 := by
    simpa only [w, norm_star] using
      ((U z j).norm_eval_le (commonStrideIndex (c z j) (m z j) (e t))).trans (hcap z j)
  obtain ⟨A, hAn, hAdense, G, j, hmass, hcorr⟩ :=
    exists_dense_common_sampled_box_of_seminorm μ F S w e he hp N hslice hw v hv hα hαone hmesh hmean
  have hDense := hAdense
  obtain ⟨b, d, K, hd, hK, hsubsetK, hdenseK, hA⟩ := hAdense
  have hnorm (z : Ω) (hz : z ∈ G) :
      Real.exp (-((q + C) ^ C)) ≤ finiteSupportGowersNorm (s + 1) (integerBox K)
        (fun x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x)) := by
    exact hdetect (D z (j z)) q hq hI (U z (j z)) (hU z (j z)) e he A (S z (j z))
      (c z (j z)) b (m z (j z)) d (H z (j z)) K (hm z (j z)) hd hK
      (hcorr z hz).1 (hS z (j z)) hA (fun t => v (F z t)) (w z (j z))
      (fun t => hv _) (fun _ _ => rfl) (hthreshold.trans (hcorr z hz).2)
  refine ⟨b, d, K, hd, hK, hsubsetK, hdenseK, ?_, ?_, ?_⟩
  · rw [← hA]
    exact hDense
  · rw [← hA]
    exact Finset.image_subset_image (Finset.subset_univ A)
  · let _ : ∀ i, NeZero (K i) := fun i => ⟨(hK i).ne'⟩
    exact sampled_normalized_cube_lower_bound (boxReduction_reflectsPairSums K) μ G s
      (fun z x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x))
      (Real.exp_nonneg _) hmass hnorm

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

theorem exists_sampled_niltest_fullbox_detection (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I]
      {Ω : Type w₁} [Fintype Ω] [Nonempty Ω] {T : Type w₂} [Fintype T] [Nonempty T]
      {X : Type w₃} {J : Ω → Type w₄} [∀ z, Nonempty (J z)]
      {L : ∀ z, J z → Type u} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
      {dim : ∀ z, J z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)] [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
      (D : ∀ z j, RationalFilteredNilmanifold (L z j) (s + 1) (dim z j))
      (U : ∀ z j, (D z j).Niltest (fun _ : I => 1))
      (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
      (S : ∀ z, J z → Finset T) (e : T → I → ℤ), Function.Injective e →
      ∀ (c : ∀ z, J z → I → ℤ) (m : ∀ z, J z → ℕ) (H : ∀ z, J z → I → ℕ),
      (∀ z j, 0 < m z j) → (∀ z j, (S z j).image e = commonStrideBox (c z j) (m z j) (H z j)) →
      ∀ (p q : ℝ) (N : I → ℕ), 0 ≤ p → 0 ≤ q → (∀ i, 0 < N i) →
      (∀ z j, IsDenseCommonStrideBox N p ((S z j).image e)) →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q →
      (∀ z j, (U z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q)) →
      (∀ z j, ((U z j).normBound : ℝ) ≤ 1) →
      ∀ (v : X → ℂ) (α : ℝ), (∀ x, ‖v x‖ ≤ 1) → 0 < α → α ≤ 1 →
      Fintype.card I * Real.exp (-p) ≤ α / 8 → Real.exp (-q) ≤ α / 4 →
      α ≤ sampledSliceSeminorm μ F S
        (fun z j t => star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))) v →
      (Real.exp (-((5 * p + 20) * Fintype.card I + p + 2)) * (α / 2)) *
        Real.exp (-denseBoxGowersTransferCost s (Fintype.card I) (p + 1) ((q + C) ^ C)) ^
          (2 ^ (s + 2)) ≤
        (μ.complexMean (fun z => normalizedSupportedCubeSum (s + 2) (integerBox N)
          (fun _ x => finiteSiteExtension e (fun t => v (F z t)) x))).re := by
  obtain ⟨C, hC, hdetect⟩ := exists_finite_site_niltest_detection (s + 1) P
  refine ⟨C, hC, ?_⟩
  intro I _ _ Ω _ _ T _ _ X J _ L _ _ dim _ _ _ _ D U μ F S e he c m H hm hS p q N hp hq
    hN hslice hI hU hcap v α hv hα hαone hmesh hthreshold hmean
  let w : ∀ z, J z → T → ℂ := fun z j t =>
    star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))
  have hw (z) (j) (t) : ‖w z j t‖ ≤ 1 := by
    simpa only [w, norm_star] using
      ((U z j).norm_eval_le (commonStrideIndex (c z j) (m z j) (e t))).trans (hcap z j)
  obtain ⟨A, hAn, hAdense, G, j, hmass, hcorr⟩ :=
    exists_dense_common_sampled_box_of_seminorm μ F S w e he hp N hslice hw v hv hα hαone hmesh hmean
  have hDense := hAdense
  obtain ⟨b, d, K, hd, hK, _, _, hA⟩ := hAdense
  let : ∀ i, NeZero (N i) := fun i => ⟨(hN i).ne'⟩
  have hnorm (z : Ω) (hz : z ∈ G) :
      Real.exp (-denseBoxGowersTransferCost s (Fintype.card I) (p + 1) ((q + C) ^ C)) ≤
        finiteSupportGowersNorm (s + 2) (integerBox N)
          (fun x => finiteSiteExtension e (fun t => v (F z t)) x) := by
    have hlocal : Real.exp (-((q + C) ^ C)) ≤ finiteSupportGowersNorm (s + 2) (integerBox K)
        (fun x => finiteSiteExtension e (fun t => v (F z t)) (commonStridePoint b d x)) :=
      hdetect (D z (j z)) q hq hI (U z (j z)) (hU z (j z)) e he A (S z (j z))
        (c z (j z)) b (m z (j z)) d (H z (j z)) K (hm z (j z)) hd hK
        (hcorr z hz).1 (hS z (j z)) hA (fun t => v (F z t)) (w z (j z))
        (fun t => hv _) (fun _ _ => rfl) (hthreshold.trans (hcorr z hz).2)
    have hdense : IsDenseCommonStrideBox N (p + 1) (commonStrideBox b d K) := by
      rw [← hA]
      exact hDense
    have hlocal' : Real.exp (-((q + C) ^ C)) ≤
        finiteSupportGowersNorm (s + 2) (commonStrideBox b d K)
          (finiteSiteExtension e (fun t => v (F z t))) := by
      rwa [finiteSupportGowersNorm_commonStride (s + 2) b hd K]
    exact denseBox_gowers_transfer s N (by linarith) (by positivity) hdense
      (finiteSiteExtension e (fun t => v (F z t)))
      (fun x _ => finiteSiteExtension_norm_le e _ (fun t => hv _) x) hlocal'
  exact sampled_normalized_cube_lower_bound (boxReduction_reflectsPairSums N) μ G (s + 1)
    (fun z x => finiteSiteExtension e (fun t => v (F z t)) x) (Real.exp_nonneg _) hmass hnorm

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

theorem exists_sampled_niltest_fullbox_detection_uniform (s : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {I : Type v} [Fintype I] [DecidableEq I]
      {Ω : Type w₁} [Fintype Ω] [Nonempty Ω] {T : Type w₂} [Fintype T] [Nonempty T]
      {X : Type w₃} {J : Ω → Type w₄} [∀ z, Nonempty (J z)]
      {L : ∀ z, J z → Type u} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
      {dim : ∀ z, J z → ℕ}
      [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)] [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
      [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
      (D : ∀ z j, RationalFilteredNilmanifold (L z j) (s + 1) (dim z j))
      (U : ∀ z j, (D z j).Niltest (fun _ : I => 1))
      (μ : FiniteProbabilityWeights Ω) (F : Ω → T → X)
      (S : ∀ z, J z → Finset T) (e : T → I → ℤ), Function.Injective e →
      ∀ (c : ∀ z, J z → I → ℤ) (m : ∀ z, J z → ℕ) (H : ∀ z, J z → I → ℕ),
      (∀ z j, 0 < m z j) → (∀ z j, (S z j).image e = commonStrideBox (c z j) (m z j) (H z j)) →
      ∀ (p q : ℝ) (N : I → ℕ), 0 ≤ p → 0 ≤ q → (∀ i, 0 < N i) →
      (∀ z j, IsDenseCommonStrideBox N p ((S z j).image e)) →
      (Fintype.card I : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q →
      (∀ z j, (U z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q)) →
      (∀ z j, ((U z j).normBound : ℝ) ≤ 1) →
      ∀ (v : X → ℂ) (α : ℝ), (∀ x, ‖v x‖ ≤ 1) → 0 < α → α ≤ 1 →
      Fintype.card I * Real.exp (-p) ≤ α / 8 → Real.exp (-q) ≤ α / 4 →
      α ≤ sampledSliceSeminorm μ F S
        (fun z j t => star ((U z j).eval (commonStrideIndex (c z j) (m z j) (e t)))) v →
      Real.exp (-((p + q + C) ^ C)) ≤
        (μ.complexMean (fun z => normalizedSupportedCubeSum (s + 2) (integerBox N)
          (fun _ x => finiteSiteExtension e (fun t => v (F z t)) x))).re := by
  obtain ⟨C₀, hC₀, hdetect⟩ := exists_sampled_niltest_fullbox_detection s P
  obtain ⟨C, hC, hbudget⟩ := exists_sampledFullboxDetection_budget s C₀ P
  refine ⟨C, hC, ?_⟩
  intro I _ _ Ω _ _ T _ _ X J _ L _ _ dim _ _ _ _ D U μ F S e he c m H hm hS p q N hp hq
    hN hslice hI hU hcap v α hv hα hαone hmesh hthreshold hmean
  have hwhole := hdetect D U μ F S e he c m H hm hS p q N hp hq hN hslice hI hU hcap
    v α hv hα hαone hmesh hthreshold hmean
  have hcost := hbudget p q (Fintype.card I) hp hq hI
  exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
    ((sampledFullboxDetection_exp_lower s C₀ (Fintype.card I) p q α hthreshold).trans hwhole)

end Erdos3

end

section

namespace Erdos3

noncomputable def sampledSlicedDetectionConstant (s : ℕ) (P : Polynomial ℕ) : ℕ :=
  Classical.choose (exists_sampled_niltest_cube_detection.{0,0,0,0,0,0} s P)

theorem sampledSlicedDetectionConstant_two_le (s : ℕ) (P : Polynomial ℕ) :
    2 ≤ sampledSlicedDetectionConstant s P :=
  (Classical.choose_spec (exists_sampled_niltest_cube_detection.{0,0,0,0,0,0} s P)).1

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_niltest_sliced_detection
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) s (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f) :
    ∃ (c₀ : LayerSamplerVariables G I n B → ℤ) (step₀ : ℕ)
      (H₀ : LayerSamplerVariables G I n B → ℕ) (_hstep₀ : 0 < step₀) (hH₀ : ∀ k, 0 < H₀ k),
      IsDenseCommonStrideBox sides (p + 1) (commonStrideBox c₀ step₀ H₀) ∧
      commonStrideBox c₀ step₀ H₀ ⊆ Finset.univ.image e ∧
      (Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
        Real.exp (-((q + sampledSlicedDetectionConstant s P) ^ sampledSlicedDetectionConstant s P)) ^
          (2 ^ (s + 1)) ≤
        (allocatedSlicedCubeSource (dim := s + 1) B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases H₀ hH₀ c₀ step₀ f).re := by
  obtain ⟨z, _⟩ := (pathLaw).exists_weight_pos
  let : Nonempty Path := ⟨z⟩
  obtain ⟨c₀, step₀, H₀, hstep₀, hH₀, hdense₀, hcover₀, hcube⟩ :=
    (Classical.choose_spec (exists_sampled_niltest_cube_detection.{0,0,0,0,0,0} s P)).2
      D V (pathLaw) (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val))
      slices e he c step H hstep hslices p q sides hp hq hdense hdimension hcomplexity hcap
      f α hf hα hαone hmesh hthreshold hdetected
  have hcover' (t) (ht : t ∈ integerBox H₀) : ∃ u, e u = commonStridePoint c₀ step₀ t := by
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp (hcover₀ (commonStridePoint_mem c₀ step₀ H₀ ht))
    exact ⟨u, hu⟩
  have hext (z : Path) :
      normalizedSupportedCubeSum (s + 1) (integerBox H₀)
        (fun _ t => finiteSiteExtension e
          (fun u => f (jointIntegerPhysicalSite (e u) (z.1.val, z.2.val))) (commonStridePoint c₀ step₀ t)) =
      normalizedSupportedCubeSum (s + 1) (integerBox H₀)
        (fun _ t => f (jointIntegerPhysicalSite (commonStridePoint c₀ step₀ t) (z.1.val, z.2.val))) := by
    exact normalizedSupportedCubeSum_finiteSiteExtension_on_map (s + 1) (integerBox H₀)
      e he (commonStridePoint c₀ step₀) hcover'
      (fun t => f (jointIntegerPhysicalSite t (z.1.val, z.2.val)))
  simp only [hext] at hcube
  rw [allocatedOriginalPathLaw_sliced_cube_source B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal H₀ hH₀ c₀ step₀ f] at hcube
  exact ⟨c₀, step₀, H₀, hstep₀, hH₀, hdense₀, hcover₀, hcube⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

noncomputable def sampledFullboxDetectionConstant (s : ℕ) (P : Polynomial ℕ) : ℕ :=
  Classical.choose (exists_sampled_niltest_fullbox_detection_uniform.{0,0,0,0,0,0} s P)

theorem sampledFullboxDetectionConstant_two_le (s : ℕ) (P : Polynomial ℕ) :
    2 ≤ sampledFullboxDetectionConstant s P :=
  (Classical.choose_spec (exists_sampled_niltest_fullbox_detection_uniform.{0,0,0,0,0,0} s P)).1

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {s : ℕ} (X : Type) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "kernelLaw" => FiniteProbabilityWeights.pi
  (fun _ : G => integerScalarCubeWeights (Fin (s + 2)) S.value S.positive)

local notation "Path" => bases × rectangularWeightIndices 0 widths 1
local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedOriginalPathLaw_niltest_selection
    (P : Polynomial ℕ)
    {T : Type} [Fintype T] [Nonempty T]
    (e : T → LayerSamplerVariables G I n B → ℤ) (he : Function.Injective e)
    (hcover : ∀ t ∈ integerBox sides, ∃ u, e u = t)
    {Tests : Path → Type} [∀ z, Nonempty (Tests z)]
    {L : ∀ z, Tests z → Type} [∀ z j, LieRing (L z j)] [∀ z j, LieAlgebra ℚ (L z j)]
    {dims : ∀ z, Tests z → ℕ}
    [∀ z j, TopologicalSpace (ℝ ⊗[ℚ] L z j)]
    [∀ z j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L z j)]
    [∀ z j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L z j)] [∀ z j, T2Space (ℝ ⊗[ℚ] L z j)]
    (D : ∀ z j, RationalFilteredNilmanifold (L z j) (s + 1) (dims z j))
    (V : ∀ z j, (D z j).Niltest (fun _ : LayerSamplerVariables G I n B => 1))
    (slices : ∀ z, Tests z → Finset T)
    (c : ∀ z, Tests z → LayerSamplerVariables G I n B → ℤ)
    (step : ∀ z, Tests z → ℕ)
    (H : ∀ z, Tests z → LayerSamplerVariables G I n B → ℕ)
    (hstep : ∀ z j, 0 < step z j)
    (hslices : ∀ z j, (slices z j).image e = commonStrideBox (c z j) (step z j) (H z j))
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hdense : ∀ z j, IsDenseCommonStrideBox sides p ((slices z j).image e))
    (hdimension : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q)
    (hcomplexity : ∀ z j, (V z j).ComplexityLE (P.eval₂ (Nat.castRingHom ℝ) q))
    (hcap : ∀ z j, ((V z j).normBound : ℝ) ≤ 1)
    (f : (X → ℤ) → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (α : ℝ) (hα : 0 < α) (hαone : α ≤ 1)
    (hmesh : Fintype.card (LayerSamplerVariables G I n B) * Real.exp (-p) ≤ α / 8)
    (hthreshold : Real.exp (-q) ≤ α / 4)
    (hdetected : α ≤ sampledSliceSeminorm (pathLaw)
      (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val)) slices
      (fun z j t => star ((V z j).eval (commonStrideIndex (c z j) (step z j) (e t)))) f)
    (Good : (G → IntegerScalarCubeBox (Fin (s + 2)) S.value) → Prop)
    (genuine : ∀ x, Good x → (X → ℤ) → ℂ)
    {E η : ℝ}
    (hE : (p + q + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 5 ≤ E)
    (hη : η ≤ Real.exp (-((p + q + sampledFullboxDetectionConstant s P) ^
      sampledFullboxDetectionConstant s P + 5)))
    (hcomparison :
      ‖(pathLaw).complexMean (fun z =>
        𝔼 cube : SupportedCube (s + 2) (integerBox sides : Set (LayerSamplerVariables G I n B → ℤ)),
          physicalCubeSiteTest (integerSelfSiteTest (s + 2) f)
            (physicalCubeRootDifferences cube.val.2 cube.val.1 z.1.val z.2.val)) -
        (kernelLaw).goodPartBaseMean bases Good genuine‖ ≤ 2 * Real.exp (-E) + η) :
    ∃ (x : G → IntegerScalarCubeBox (Fin (s + 2)) S.value) (hx : Good x) (base : X → ℤ),
      0 < (kernelLaw).weight x ∧ base ∈ bases ∧
        Real.exp (-((p + q + sampledFullboxDetectionConstant s P) ^
          sampledFullboxDetectionConstant s P + 1)) ≤ (genuine x hx base).re := by
  obtain ⟨z, _⟩ := (pathLaw).exists_weight_pos
  let : Nonempty Path := ⟨z⟩
  have hparam : ∀ i, 0 < sides i := by
    intro i
    cases i with
    | inl g => exact S.positive
    | inr i => exact allocatedPrincipalSides_pos B U b S i
  have hcube := (Classical.choose_spec
    (exists_sampled_niltest_fullbox_detection_uniform.{0,0,0,0,0,0} s P)).2
    D V (pathLaw) (fun z t => jointIntegerPhysicalSite (e t) (z.1.val, z.2.val))
    slices e he c step H hstep hslices p q sides hp hq hparam hdense hdimension hcomplexity hcap
    f α hf hα hαone hmesh hthreshold hdetected
  exact allocatedOriginalPathLaw_finite_self_cube_selection B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal e he hcover f Good genuine
    (Real.exp_pos _) hcomparison ((sourceDetection_error_share hE hη).trans hcube)

end Erdos3.VectorPolynomial

end

end OAI
