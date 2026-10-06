import GowersSzemeredi.Proofs05MultilinearIteration

/-! # Lifting a multilinear function by one coordinate -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Multiplication by a new variable preserves multilinearity. -/
theorem IsMultilinear.mul_new_coordinate {N k : Nat}
    {mu : Point N k → ZMod N} (hmu : IsMultilinear mu) :
    IsMultilinear (fun z : Point N (k + 1) => mu (Fin.tail z) * z 0) := by
  classical
  obtain ⟨c, hc⟩ := hmu
  refine ⟨fun e => if e 0 then c (Fin.tail e) else 0, ?_⟩
  intro z
  dsimp only
  rw [hc]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.tail, Finset.mul_sum, mul_comm, mul_left_comm]

/-- The threshold forces the final root to be at least two, so every axis
in a partition cell contains a pair of adjacent indices. -/
theorem multilinearPartition_root_two_le {k q m : Nat} (hk : 2 ≤ k)
    (hm : multilinearPartitionThreshold k q ≤ m) :
    2 ≤ (m : Real) ^ multilinearPartitionExponent k q := by
  let E := multilinearPartitionConstant k ^ (2 ^ k * q)
  have hK := multilinearPartitionConstant_eight_le hk
  have hE : 0 < E := by dsimp [E]; positivity
  have hEr : (0 : Real) < E := by exact_mod_cast hE
  have hT : 1 ≤ polynomialPartitionThreshold k := by
    unfold polynomialPartitionThreshold weylThreshold
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpow : 2 ^ E ≤ m :=
    (Nat.pow_le_pow_left (by omega : 2 ≤ 2 * polynomialPartitionThreshold k) E).trans hm
  have hm0 : (0 : Real) < m := by exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 2 ^ E) hpow)
  have heq : multilinearPartitionExponent k q = (E : Real)⁻¹ := by
    simp [multilinearPartitionExponent, E]
  rw [heq]
  have hroot : ((m : Real) ^ (E : Real)⁻¹) ^ E = m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, inv_mul_cancel₀ hEr.ne', Real.rpow_one]
  apply le_of_pow_le_pow_left₀ hE.ne' (Real.rpow_pos_of_pos hm0 _).le
  rw [hroot]
  exact_mod_cast hpow

end LeanProofs.GowersSzemeredi
