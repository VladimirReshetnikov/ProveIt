import GowersSzemeredi.Proofs18BoundaryRefinement
import GowersSzemeredi.Proofs18IntervalBoundarySelection

/-! A discrepancy partition yields an ordinary interval density increment,
independently of the degree or method that produced the partition. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Refine a supplied discrepancy partition away from the interval boundary.
The length exponent loses a factor sixteen, and the density gain is beta/8. -/
theorem interval_density_increment_of_discrepancy_partition
    {N L M : Nat} [NeZero N] (hL : L ≤ N)
    (beta sigma : Real) (hβ : 0 < beta) (hscale : 32 ≤ beta * N)
    (A : Finset (ZMod N)) (delta : Real)
    (hAS : A ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L)))
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hcard : (A.card : Real) = delta * L)
    (Q : Fin M → ModAP N) (hQ : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hQproper : ∀ i, (Q i).IsProper)
    (havg : (N : Real) ^ sigma ≤ averageCellSize (fun i => (Q i).carrier))
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (Q i).carrier,
      relativeBalanced A (finiteIntervalImage N (Finset.univ : Finset (Fin L))) delta x‖) :
    ∃ P : ModAP N, P.IsProper ∧
      P.carrier ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L)) ∧
      (beta / (8 * boundaryRefinementConstant (beta / 64))) *
        (N : Real) ^ (sigma / 16) ≤ (P.carrier.card : Real) ∧
      (delta + beta / 8) * P.carrier.card ≤ (A ∩ P.carrier).card := by
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hC : 0 < boundaryRefinementConstant (beta / 64) := section5LocalRefinementConstant_pos _ _
  obtain ⟨K, R, hR, _, hRproper, hcount, hdiam, hnorm⟩ :=
    small_diameter_partition_refinement Q (beta / 64) (by positivity) hQ hQproper
  obtain ⟨j, hsub, hsize, hinc⟩ := interval_small_diameter_relative_increment R hL A delta beta
    hAS hδ hδone hβ hcard hR hdiam hscale (hdis.trans (hnorm _))
  have hK : (0 : Real) < K := Nat.cast_pos.mpr (section18_partition_index_nonempty _ hR)
  rw [hQ.averageCellSize_univ,
    le_div_iff₀' (Nat.cast_pos.mpr (section18_partition_index_nonempty _ hQ))] at havg
  generalize boundaryRefinementConstant (beta / 64) = C at hC hcount ⊢
  have hKN : (K : Real) * N ^ (sigma / 16) ≤ C * N := calc
    (K : Real) * N ^ (sigma / 16) ≤
        C * (M : Real) ^ (1 / 16 : Real) * (N : Real) ^ (15 / 16 : Real) * N ^ (sigma / 16) := by
      gcongr
    _ = C * ((M : Real) * N ^ sigma) ^ (1 / 16 : Real) * N ^ (15 / 16 : Real) := by
      rw [Real.mul_rpow (Nat.cast_nonneg M) (Real.rpow_nonneg hNr.le sigma),
        ← Real.rpow_mul hNr.le, show sigma * (1 / 16) = sigma / 16 by ring]
      ring
    _ ≤ C * (N : Real) ^ (1 / 16 : Real) * N ^ (15 / 16 : Real) := by gcongr
    _ = C * N := by rw [mul_assoc, ← Real.rpow_add hNr]; norm_num
  refine ⟨R j, hRproper j, hsub, le_trans ?_ hsize, hinc⟩
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith [mul_le_mul_of_nonneg_left hKN hβ.le]

end LeanProofs.GowersSzemeredi
