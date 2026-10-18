import GowersSzemeredi.Proofs17PartitionEnergy

/-! Declarations of `Proofs17PartitionEnergy` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open scoped BigOperators

/-- Failure of partition uniformity gives an individual cell with the
corresponding normalized ambient uniformity failure. This does not change
modulus or assert uniformity after an interval/prime-model transfer. -/
theorem not_uniformOnPartition_exists_cell {N M k m : Nat} [NeZero N]
    (f : ZMod N → Complex) (Q : Fin M → ModAP N) (beta : Real)
    (h : ¬ UniformOnPartition f k beta Q m) :
    ∃ i : Fin M, ¬ UniformOfDegree (restrictToCell (Q i).carrier f)
      (beta * ((m : Real) / N) ^ (k + 2)) k := by
  by_contra hn
  push Not at hn
  apply h
  unfold UniformOnPartition
  simp_rw [sum_cube_succ_eq_sum_norm_sq, Complex.ofReal_re]
  have hNne : (N : Real) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hscale : (beta * ((m : Real) / N) ^ (k + 2)) * (N : Real) ^ (k + 2) =
      beta * (m : Real) ^ (k + 2) := by
    rw [div_pow]
    field_simp
  calc
    _ ≤ ∑ _i : Fin M, beta * (m : Real) ^ (k + 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := hn i
      unfold UniformOfDegree at hi
      simpa only [hscale] using hi
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end

end LeanProofs.GowersSzemeredi
