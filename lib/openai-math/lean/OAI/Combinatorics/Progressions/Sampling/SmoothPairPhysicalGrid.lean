import OAI.Combinatorics.Progressions.Probability.CanonicalPairPointLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def smoothPairKernelBaseCap {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (C κ : ℝ) : ℝ≥0 :=
  Real.toNNReal (1 + 2 * (4 * C / κ) ^ 2 * 2 ^ Fintype.card {j : J // j ≠ k})

noncomputable def smoothPairKernelBaseLip {J : Type*} [Fintype J] [DecidableEq J]
    (k : J) (C κ : ℝ) : ℝ≥0 :=
  Real.toNNReal (2 * (4 * C / κ) ^ 3 * (smoothPairRowLipschitz k : ℝ) *
    2 ^ Fintype.card {j : J // j ≠ k})

noncomputable def smoothPairKernelCap {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) : ℝ≥0 := (smoothPairKernelBaseCap k C κ) ^ n

noncomputable def smoothPairKernelLip {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) : ℝ≥0 :=
  n * smoothPairKernelBaseLip k C κ * smoothPairKernelCap n k C κ

theorem normalized_integer_pair_dist {I : Type*} [Fintype I]
    (H : I → ℝ) (hH : ∀ i, 0 < H i) (v w c : I → Fin 2 → ℤ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ i j, |(v i j : ℝ) - (w i j : ℝ)| ≤ ρ * H i) :
    dist (fun i j => ((v i j - c i j : ℤ) : ℝ) / H i)
      (fun i j => ((w i j - c i j : ℤ) : ℝ) / H i) ≤ ρ := by
  apply (dist_pi_le_iff hρ).mpr
  intro i
  apply (dist_pi_le_iff hρ).mpr
  intro j
  rw [Real.dist_eq]
  have heq : ((v i j - c i j : ℤ) : ℝ) / H i -
      ((w i j - c i j : ℤ) : ℝ) / H i = ((v i j : ℝ) - (w i j : ℝ)) / H i := by
    push_cast
    ring
  rw [heq, abs_div, abs_of_pos (hH i)]
  exact (div_le_iff₀ (hH i)).mpr (h i j)

theorem shiftedPairLocationKernel_cap {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    {C κ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (b : Option J × I → ℤ) (x y : I → ℤ) :
    |shiftedPairLocationKernel t u k hne H L hH hL b x y| ≤
      smoothPairKernelCap (Fintype.card I) k C κ := by
  exact (smoothPairProductDensity_regularity t u k hne H L hH hL hC hκ ht hu hgap).1 _

theorem shiftedPairLocationKernel_grid_error {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    {C κ ρ : ℝ} (hC : 1 ≤ C) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (ht : |(t k : ℝ) / L| ≤ C) (hu : |(u k : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (b : Option J × I → ℤ) (x y x' y' : I → ℤ)
    (hx : ∀ i, |(x i : ℝ) - (x' i : ℝ)| ≤ ρ * H i)
    (hy : ∀ i, |(y i : ℝ) - (y' i : ℝ)| ≤ ρ * H i) :
    |shiftedPairLocationKernel t u k hne H L hH hL b x y -
      shiftedPairLocationKernel t u k hne H L hH hL b x' y'| ≤
      (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ := by
  have hd := normalized_integer_pair_dist H hH (affinePairRowsOfLocations (x, y))
    (affinePairRowsOfLocations (x', y')) (smoothAffinePairRows t u b) hρ (fun i j => by
      fin_cases j
      · exact hx i
      · exact hy i)
  have hlip : LipschitzWith (smoothPairKernelLip (Fintype.card I) k C κ)
      (smoothPairProductDensity t u k hne H L hH hL) :=
    (smoothPairProductDensity_regularity t u k hne H L hH hL hC hκ ht hu hgap).2
  exact (hlip.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left hd (NNReal.coe_nonneg _))

end Erdos3

end

end OAI
