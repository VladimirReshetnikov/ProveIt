import OAI.Combinatorics.Progressions.Lattices.AffineWindowGoodKernelBound

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem scalarCubeWindowResidueSet_full_one (I : Type*) [Fintype I] (L : ℕ)
    (r : Option I → ZMod 1) :
    scalarCubeWindowResidueSet I L L (fun _ => 1) r = integerScalarCubeSet I L := by
  ext x
  rw [mem_scalarCubeWindowResidueSet, mem_integerScalarCubeSet]
  exact and_iff_left (fun i => Subsingleton.elim _ _)

theorem scalarCubeWindowWeights_full_one (I : Type*) [Fintype I] [DecidableEq I]
    (L M D : ℕ) (hL : 0 < L) (hD : L ≤ D * L) (hM : 1 ≤ M)
    (r : Option I → ZMod 1) (hsize : (Fintype.card I + 1) * M ≤ L) :
    scalarCubeWindowWeights I L L M D hL le_rfl hD (fun _ => 1) r
      (fun _ => Nat.zero_lt_one) (fun _ => hM) hsize = integerScalarCubeWeights I L hL := by
  unfold scalarCubeWindowWeights
  simp only [scalarCubeWindowResidueSet_full_one]
  unfold integerScalarCubeWeights
  rw [FiniteProbabilityWeights.condition_condition]
  simp only [Finset.inter_self]

theorem affineScalarCubeWindowWeights_full_one (I : Type*) [Fintype I] [DecidableEq I]
    (L M D : ℕ) (c : ℤ) (hL : 0 < L) (hD : L ≤ D * L) (hM : 1 ≤ M)
    (r : Option I → ZMod 1) (hsize : (Fintype.card I + 1) * M ≤ L) :
    affineScalarCubeWindowWeights I L L M D c hL le_rfl hD (fun _ => 1) r
      (fun _ => Nat.zero_lt_one) (fun _ => hM) hsize = integerScalarCubeWeights I L hL := by
  unfold affineScalarCubeWindowWeights
  exact scalarCubeWindowWeights_full_one I L M D hL hD hM _ hsize

end Erdos3

end

end OAI
