/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.UniformBoxResidueMass
import OAI.Combinatorics.Progressions.Linear.SmoothPairKernel

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def fullSmoothPairError {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ δ : ℝ) : ℝ :=
  n * smoothPairProbabilityError k Q C κ δ *
    (smoothPairProbabilityCap k Q C κ + smoothPairProbabilityError k Q C κ δ) ^ n

noncomputable def shiftedPairLocationKernel {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) (L : ℝ) (hH : ∀ i, 0 < H i) (hL : 0 < L)
    (b : Option J × I → ℤ) (x y : I → ℤ) : ℝ :=
  smoothPairProductDensity t u k hne H L hH hL
    (fun i j => ((affinePairRowsOfLocations (x, y) i j - smoothAffinePairRows t u b i j : ℤ) : ℝ) / H i)

theorem canonical_pair_point_error {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (x y : I → ℤ)
    (hxy : integerVectorResidue (affinePairModulus t u) x = integerVectorResidue (affinePairModulus t u) y) :
    |(∏ i, H i ^ 2) *
        ((shiftedSmoothProductPMF (fun z => (b z : ℝ))
          (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
          (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).map
          (smoothAffinePairRows t u) (affinePairRowsOfLocations (x, y))).toReal -
      (affinePairModulus t u : ℝ) ^ Fintype.card I *
        shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x y| ≤
      (affinePairModulus t u : ℝ) ^ Fintype.card I * fullSmoothPairError (Fintype.card I) k Q C κ δ := by
  have hraw := shifted_anisotropic_smooth_pair_product_probability_law t u k hne H Q hH hL hC hκ
    hδ hδ1 ht hu hgap hQ hmesh hsmall b hZ (affinePairRowsOfLocations (x, y))
  have hmask : ∀ i, BohrLattice.Primitive.content (fun j => u j - t j) ∣
      affinePairRowsOfLocations (x, y) i 1 - affinePairRowsOfLocations (x, y) i 0 :=
    (affinePairModulus_residue_iff t u x y).mp hxy
  rw [ite_eq_left hmask] at hraw
  have h : |(∏ i, H i ^ 2) *
        ((shiftedSmoothProductPMF (fun z => (b z : ℝ))
          (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
          (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).map
          (smoothAffinePairRows t u) (affinePairRowsOfLocations (x, y))).toReal -
      (affinePairModulus t u : ℝ) ^ Fintype.card I *
        shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x y| ≤
      fullSmoothPairError (Fintype.card I) k Q C κ δ := by
    simpa only [fullSmoothPairError, affinePairModulus, shiftedPairLocationKernel, smoothPairProductDensity] using hraw
  have hE : 0 ≤ fullSmoothPairError (Fintype.card I) k Q C κ δ := (abs_nonneg _).trans h
  have hbase : (1 : ℝ) ≤ affinePairModulus t u := by
    exact_mod_cast Nat.succ_le_of_lt (affinePairModulus_pos t u k hne)
  have hN : (1 : ℝ) ≤ (affinePairModulus t u : ℝ) ^ Fintype.card I := one_le_pow₀ hbase
  apply h.trans
  nlinarith [mul_nonneg (sub_nonneg.mpr hN) hE]

end Erdos3

end

end OAI
