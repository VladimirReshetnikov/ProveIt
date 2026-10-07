import OAI.Combinatorics.Progressions.Geometry.PhysicalBoxControl

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem ordinaryMesh_marginals_of_lengths {ι I : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hpos : ∀ i c, 0 < (P i).length c) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    (b : ℕ) (modLog dimLog accLog lengthLog eta : ℝ)
    (hmod : 0 ≤ modLog) (heta : eta ≤ 1) (hacc : Real.exp (-accLog) ≤ eta)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlog : modLog * (b : ℝ) + accLog + dimLog + 1 ≤ lengthLog)
    (hlength : ∀ i c, Real.exp lengthLog ≤ ((P i).length c : ℝ))
    (c : ∀ i, (P i).Label) :
    ProductMarginalsClose (primeCoordinateReference (σ := I) q)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => (P i).length (c i)) 1 (fun _ => 0)
        (physicalBoxCell_nonempty lo N P hpos c) q (fun _ => 1)) eta b := by
  apply residuePrimeDensity_close_of_lengths _ _ 1 _ _ q (by norm_num)
    (fun _ => by simp) hpair b modLog dimLog accLog eta hmod heta hacc hmoduli hdim
  intro i
  simp only [Nat.cast_one, residueIndexLength_one_zero]
  exact (Real.exp_le_exp.mpr hlog).trans (hlength i (c i))

end Erdos3

end

end OAI
