import OAI.Combinatorics.Progressions.Estimates.LocalMajorSliceSites

namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

theorem integerPoints_subset_integerBox (A : ResidueBoxSlice N q) :
    A.integerPoints ⊆ integerBox N := by
  classical
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  apply (mem_integerBox N _).mpr
  intro i
  change 0 ≤ ((A.point j i).val : ℤ) ∧ ((A.point j i).val : ℤ) < (N i : ℤ)
  exact ⟨Int.natCast_nonneg _, by exact_mod_cast (A.point j i).isLt⟩

noncomputable def subtypeSites (A : ResidueBoxSlice N q) : Finset ↥(integerBox N) := by
  classical
  exact Finset.univ.filter (fun x => x.val ∈ A.integerPoints)

@[simp] theorem mem_subtypeSites (A : ResidueBoxSlice N q) (x : integerBox N) :
    x ∈ A.subtypeSites ↔ x.val ∈ A.integerPoints := by
  classical
  simp only [subtypeSites, Finset.mem_filter, Finset.mem_univ, true_and]

theorem subtypeSites_image_val (A : ResidueBoxSlice N q) :
    A.subtypeSites.image Subtype.val = A.integerPoints := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (A.mem_subtypeSites t).mp ht
  · intro hx
    exact Finset.mem_image.mpr ⟨⟨x, A.integerPoints_subset_integerBox hx⟩,
      (A.mem_subtypeSites _).mpr hx, rfl⟩

theorem expect_subtypeSites (A : ResidueBoxSlice N q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : (I → ℤ) → V) :
    (𝔼 t ∈ A.subtypeSites, f t.val) = 𝔼 x ∈ A.integerPoints, f x := by
  classical
  rw [← A.subtypeSites_image_val]
  exact (Finset.expect_image Subtype.val_injective.injOn).symm

theorem subtypeSites_nonempty_of_integerPoints (A : ResidueBoxSlice N q)
    (h : A.integerPoints.Nonempty) : A.subtypeSites.Nonempty := by
  classical
  rw [← A.subtypeSites_image_val, Finset.image_nonempty] at h
  exact h

theorem subtypeSites_nonempty (A : ResidueBoxSlice N q) (hA : ∀ i, 0 < A.length i) :
    A.subtypeSites.Nonempty := by
  classical
  apply A.subtypeSites_nonempty_of_integerPoints
  let j : ∀ i, Fin (A.length i) := fun i => ⟨0, hA i⟩
  exact ⟨A.integerPoint j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

theorem subtypeSites_dense (A : ResidueBoxSlice N q) {cost : ℝ}
    (h : IsDenseCommonStrideBox N cost A.integerPoints) :
    IsDenseCommonStrideBox N cost (A.subtypeSites.image Subtype.val) := by
  classical
  rw [A.subtypeSites_image_val]
  exact h

end Erdos3.ResidueBoxSlice

namespace Erdos3

open scoped BigOperators TensorProduct

theorem productive_localMajorSubtypeSlice_mass_le_sampledSliceSeminorm
    {Ω I X L : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {J : Ω → Type*} (D : RationalFilteredNilmanifold L s d)
    (law : FiniteProbabilityWeights Ω) (good : Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (q : ∀ z, J z → ℕ) (A : ∀ z j, ResidueBoxSlice N (q z j))
    (tests : ∀ z, J z → D.Niltest (fun _ : I => 1))
    (physical : Ω → ↥(integerBox N) → X) (signal : X → ℂ) (cost : ℝ)
    (hdense : ∀ z j, IsDenseCommonStrideBox N cost (A z j).integerPoints)
    (hcap : ∀ z j, ((tests z j).normBound : ℝ) ≤ 1)
    (hcorr : ∀ z ∈ good, ∃ j : J z,
      (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ (A z j).subtypeSites,
        signal (physical z x) * star ((tests z j).eval
          (commonStrideIndex (fun i => ((A z j).start i : ℤ)) (q z j) x.val))‖) :
    (9 / 10 : ℝ) * law.mass good ≤ sampledSliceSeminorm law physical
      (fun z j => (A z j).subtypeSites)
      (fun z j x => star ((tests z j).eval
        (commonStrideIndex (fun i => ((A z j).start i : ℤ)) (q z j) x.val))) signal := by
  classical
  let : Nonempty ↥(integerBox N) := ⟨⟨fun _ => 0, (mem_integerBox N _).mpr
    (fun i => ⟨le_rfl, by exact_mod_cast hN i⟩)⟩⟩
  apply productive_mass_mul_le_sampledSliceSeminorm law good physical
    (fun z j => (A z j).subtypeSites)
    (fun z j x => star ((tests z j).eval
      (commonStrideIndex (fun i => ((A z j).start i : ℤ)) (q z j) x.val)))
    (fun z j => (A z j).subtypeSites_nonempty_of_integerPoints (hdense z j).nonempty)
    _ signal (9 / 10) hcorr
  intro z j x
  simpa only [norm_star] using ((tests z j).norm_eval_le
    (commonStrideIndex (fun i => ((A z j).start i : ℤ)) (q z j) x.val)).trans (hcap z j)

end Erdos3

end

end OAI
