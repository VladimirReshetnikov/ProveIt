import OAI.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration

namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace ResidueBoxSlice

abbrev wholeBox {X : Type*} (N : X → ℕ) : ResidueBoxSlice N 1 where
  start _ := 0
  length := N
  inside _ _ hj := by simpa using hj

@[simp] theorem wholeBox_point {X : Type*} (N : X → ℕ)
    (x : ∀ i, Fin (N i)) : (wholeBox N).point x = x := by
  funext i
  apply Fin.ext
  simp [wholeBox, point]

@[simp] theorem wholeBox_integerPoint {X : Type*} (N : X → ℕ)
    (x : ∀ i, Fin (N i)) :
    (wholeBox N).integerPoint x = fun i => ((x i).val : ℤ) := by
  funext i
  change ((0 + 1 * (x i).val : ℕ) : ℤ) = ((x i).val : ℤ)
  simp

@[simp] theorem wholeBox_integerPoints {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) : (wholeBox N).integerPoints = integerBox N := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    rw [wholeBox_integerPoint, mem_integerBox]
    intro i
    exact ⟨by positivity, by exact_mod_cast (j i).isLt⟩
  · intro hx
    have hx' := (mem_integerBox N x).mp hx
    let j : ∀ i, Fin (N i) := fun i => ⟨(x i).toNat, by
      have hi := hx' i
      omega⟩
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    rw [wholeBox_integerPoint]
    funext i
    exact Int.toNat_of_nonneg (hx' i).1

end ResidueBoxSlice

@[simp] theorem relativePatchSliceScore_wholeBox {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ)
    (A : PolynomialPatch X s d) :
    relativePatchSliceScore (ResidueBoxSlice.wholeBox N) f target A =
      relativePatchBoxScore N f target A := by
  have h := (ResidueBoxSlice.wholeBox N).expect_integerPoints (by decide : 0 < 1)
    (fun x => (f x - target) * A.value (fun i => (x i : ℝ)))
  rw [ResidueBoxSlice.wholeBox_integerPoints] at h
  simp only [ResidueBoxSlice.wholeBox_integerPoint, Int.cast_natCast] at h
  simp only [relativePatchSliceScore, relativePatchBoxScore,
    ResidueBoxSlice.wholeBox_point]
  convert h.symm using 1
  apply Finset.expect_congr
  · ext x
    simp
  · intro x _
    rfl

theorem relativePatchSliceConclusion_of_boxScore {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (target cost : ℝ)
    (A : PolynomialPatch X s d) (hcost : 0 ≤ cost)
    (hcomplexity : relativePatchComplexity A ≤ cost)
    (hscore : Real.exp (-cost) ≤ relativePatchBoxScore N f target A) :
    RelativePatchSliceConclusion s N f target d cost := by
  refine ⟨1, by decide, ResidueBoxSlice.wholeBox N, d, A, ?_, le_rfl,
    hcomplexity, ?_⟩
  · intro i
    change Real.exp (-cost) * (N i : ℝ) ≤ (N i : ℝ)
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))
  · simpa only [relativePatchSliceScore_wholeBox] using hscore

theorem relativePatchBoxScore_eq_subtype {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ)
    (A : PolynomialPatch X s d) :
    relativePatchBoxScore N f target A =
      (𝔼 x : ↥(integerBox N), (f x.val - target) * A.value (fun i => (x.val i : ℝ))) := by
  classical
  symm
  apply Finset.expect_nbij (fun x : ↥(integerBox N) => x.val)
  · intro x _
    exact x.property
  · intro x _
    rfl
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

theorem relativePatchSliceConclusion_of_subtypeScore {X : Type*}
    [Fintype X] [DecidableEq X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (target cost : ℝ)
    (A : PolynomialPatch X s d) (hcost : 0 ≤ cost)
    (hcomplexity : relativePatchComplexity A ≤ cost)
    (hscore : Real.exp (-cost) ≤
      (𝔼 x : ↥(integerBox N), (f x.val - target) * A.value (fun i => (x.val i : ℝ)))) :
    RelativePatchSliceConclusion s N f target d cost := by
  apply relativePatchSliceConclusion_of_boxScore N f target cost A hcost hcomplexity
  simpa only [relativePatchBoxScore_eq_subtype] using hscore

end Erdos3

end

end OAI
