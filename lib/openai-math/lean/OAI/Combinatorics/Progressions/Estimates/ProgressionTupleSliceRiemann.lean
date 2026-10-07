import OAI.Combinatorics.Progressions.Lattices.AffineKernelEndpointGeometry

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]

theorem progressionTuple_residue_riemann
    (L step H M : J → ℕ) (c : J → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (modulus : J → Option I → ℕ) (residue : ∀ j i, ZMod (modulus j i))
    (hm : ∀ j i, 0 < modulus j i) (hmM : ∀ j i, modulus j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1) * M j ≤ H j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ) / H j) < volume.real (scalarCubeDomain I))
    {ε : ℝ} (hε : 0 ≤ ε) (hmesh : ∀ j, (step j : ℝ) / L j ≤ ε)
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzWith K φ) (hA : 0 ≤ A) (hb : ∀ x, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (H j) (M j)
        (by have := hH j; omega) (modulus j) (residue j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i =>
          ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j)) -
      ∫ x, φ (affineCubeTuple (fun j => (c j : ℝ) / L j)
        (fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j) x) ∂scalarCubeProductMeasure J I| ≤
      (2 * A * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K * 2) *
        ∑ j, (M j : ℝ) / H j + K * ε := by
  have hHp (j) : 0 < H j := by have := hH j; omega
  let lower := fun j => (c j : ℝ) / L j
  let w := fun j => (step j : ℝ) * H j / L j
  let v := fun j => (step j : ℝ) * ((H j : ℝ) - 1) / L j
  have hw (j) : |w j| ≤ (2 : ℝ≥0) := by
    have he := (progression_slice_geometry (c j) (hL j) (hstep j) (hH j) hδ (hsubset j) (hdense j)).2.1
    dsimp only [w]
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by exact_mod_cast hL j : (0 : ℝ) < L j)).mpr
    simpa only [Nat.cast_mul, NNReal.coe_ofNat] using he.le
  have hv (j) : |w j - v j| ≤ ε := by
    have he : w j - v j = (step j : ℝ) / L j := by dsimp [w, v]; ring
    rw [he, abs_of_nonneg (by positivity)]
    exact hmesh j
  have he := affineCubeTuple_residue_riemann H M hHp modulus residue hm hmM hsize hsmall
    lower w v 2 hw hε hv φ hφ hA hb
  have hid (z : ∀ j, IntegerScalarCubeBox I (H j)) :
      affineCubeTuple lower w (fun j i => (z j i : ℝ) / H j) =
        fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (z j i : ℝ)) / L j := by
    funext j i
    have hH0 : (H j : ℝ) ≠ 0 := by exact_mod_cast (hHp j).ne'
    dsimp only [affineCubeTuple, lower, w]
    split_ifs <;> field_simp
    ring
  simp_rw [hid] at he
  exact he

end Erdos3

end

end OAI
