import OAI.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {ι : Type*} [Fintype ι]

theorem real_fourCoordinateKernel_mem_iff (S : Finset (Fin 4))
    (x : ℝ ⊗[ℚ] (Fin 4 → ι → ℚ)) :
    x ∈ (fourCoordinateKernel (V := ι → ℚ) S).baseChange ℝ ↔
      ∀ k ∈ S, ∀ i, DegreeRankLieFiltration.realFourCoordinateEquiv x ⟨k, i⟩ = 0 := by
  have hker : fourCoordinateKernel (V := ι → ℚ) S =
      ⨅ k : S, LinearMap.ker (LinearMap.proj (k : Fin 4) : (Fin 4 → ι → ℚ) →ₗ[ℚ] (ι → ℚ)) := by
    ext v
    constructor
    · intro hv
      apply (Submodule.mem_iInf _).mpr
      intro k
      exact (mem_fourCoordinateKernel S v).mp hv k k.property
    · intro hv
      apply (mem_fourCoordinateKernel S v).mpr
      intro k hk
      exact (Submodule.mem_iInf _).mp hv ⟨k, hk⟩
  rw [hker, real_baseChange_iInf]
  constructor
  · intro hx k hk i
    have hz := (Submodule.mem_iInf _).mp hx ⟨k, hk⟩
    rw [realification_ker] at hz
    have hzero : (LinearMap.proj k : (Fin 4 → ι → ℚ) →ₗ[ℚ] (ι → ℚ)).baseChange ℝ x = 0 := hz
    rw [← realCoordinate_projection]
    simpa only [map_zero, Pi.zero_apply] using
      congrFun (congrArg realRationalCoordinateEquiv hzero) i
  · intro hx
    apply (Submodule.mem_iInf _).mpr
    intro k
    rw [realification_ker]
    change (LinearMap.proj (k : Fin 4) : (Fin 4 → ι → ℚ) →ₗ[ℚ] (ι → ℚ)).baseChange ℝ x = 0
    apply realRationalCoordinateEquiv.injective
    funext i
    simpa only [map_zero, Pi.zero_apply, realCoordinate_projection] using hx k k.property i

theorem mem_realSparseFirstProjection_of_zero
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (S : Finset (Fin 4))
    (y : (Σ _ : Fin 4, ι) → ℝ) (hy : y ∈ realFourCoordinateSpan J)
    (hzero : ∀ k ∈ S, ∀ i, y ⟨k, i⟩ = 0) :
    (fun i => y ⟨0, i⟩) ∈ realRationalCoordinateSpan (fourSparseFirstProjection J S) := by
  obtain ⟨x, hx, rfl⟩ := hy
  have hxK := (real_fourCoordinateKernel_mem_iff S x).mpr hzero
  have hxJK : x ∈ (J ⊓ fourCoordinateKernel S).baseChange ℝ := by
    rw [realification_inf]
    exact ⟨hx, hxK⟩
  have hproj : (LinearMap.proj (0 : Fin 4)).baseChange ℝ x ∈
      (fourSparseFirstProjection J S).baseChange ℝ := by
    change _ ∈ ((J ⊓ fourCoordinateKernel S).map (LinearMap.proj 0)).baseChange ℝ
    rw [realification_map]
    exact ⟨x, hxJK, rfl⟩
  have hmem : realRationalCoordinateEquiv ((LinearMap.proj (0 : Fin 4)).baseChange ℝ x) ∈
      realRationalCoordinateSpan (fourSparseFirstProjection J S) := ⟨_, hproj, rfl⟩
  have heq : realRationalCoordinateEquiv ((LinearMap.proj (0 : Fin 4)).baseChange ℝ x) =
      fun i => DegreeRankLieFiltration.realFourCoordinateEquiv x ⟨0, i⟩ := by
    funext i
    exact realCoordinate_projection x 0 i
  rwa [heq] at hmem

theorem realRationalCoordinateSpan_inf (U V : Submodule ℚ (ι → ℚ)) :
    realRationalCoordinateSpan (U ⊓ V) =
      realRationalCoordinateSpan U ⊓ realRationalCoordinateSpan V := by
  unfold realRationalCoordinateSpan
  rw [realification_inf]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hv⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, ⟨x, hv, rfl⟩⟩
  · rintro ⟨⟨x, hx, hxy⟩, ⟨z, hz, hzy⟩⟩
    have hxz : x = z := realRationalCoordinateEquiv.injective (hxy.trans hzy.symm)
    exact ⟨x, ⟨hx, hxz.symm ▸ hz⟩, hxy⟩

theorem real_fourDependentProjection_eq (J : Submodule ℚ (Fin 4 → ι → ℚ)) :
    realRationalCoordinateSpan (fourDependentProjection J) =
      realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) ⊓
        realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) :=
  realRationalCoordinateSpan_inf _ _

end Erdos3

end

end OAI
