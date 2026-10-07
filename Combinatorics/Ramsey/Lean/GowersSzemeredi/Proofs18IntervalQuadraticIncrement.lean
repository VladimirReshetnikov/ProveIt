import GowersSzemeredi.Proofs18BoundaryRefinement
import GowersSzemeredi.Proofs18IntervalBoundarySelection
import GowersSzemeredi.Proofs18QuadraticDichotomy

/-! A quadratic density increment on a proper progression contained in the
original interval. The original relative density is retained. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Refining away interval-boundary crossings gives a genuine progression
inside the support, with explicit size and relative-density increment. -/
theorem interval_quadratic_density_increment
    (alpha : Real) (hα : 0 < alpha) (hαone : alpha ≤ 1)
    (N L : Nat) [NeZero N] [Fact N.Prime] (hL : L ≤ N)
    (hN : quadraticExponentialThreshold alpha ≤ N)
    (hscale : 32 ≤ quadraticDiscrepancyParameter alpha * N)
    (A : Finset (ZMod N)) (delta : Real)
    (hAS : A ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L)))
    (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hcard : (A.card : Real) = delta * L)
    (hnot : ¬ UniformOfDegree
      (relativeBalanced A (finiteIntervalImage N (Finset.univ : Finset (Fin L))) delta) alpha 2) :
    ∃ P : ModAP N, P.IsProper ∧
      P.carrier ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L)) ∧
      (quadraticDiscrepancyParameter alpha /
          (8 * boundaryRefinementConstant (quadraticDiscrepancyParameter alpha / 64))) *
        (N : Real) ^ (quadraticDiscrepancyExponent alpha / 16) ≤ (P.carrier.card : Real) ∧
      (delta + quadraticDiscrepancyParameter alpha / 8) * P.carrier.card ≤ (A ∩ P.carrier).card := by
  let S := finiteIntervalImage N (Finset.univ : Finset (Fin L))
  let f := relativeBalanced A S delta
  let beta := quadraticDiscrepancyParameter alpha
  let sigma := quadraticDiscrepancyExponent alpha
  let C := boundaryRefinementConstant (beta / 64)
  have hβ : 0 < beta := by dsimp [beta, quadraticDiscrepancyParameter]; positivity
  have hC : 0 < C := section5LocalRefinementConstant_pos _ _
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨M, Q, hQ, hQproper, havg, hdis⟩ :=
    quadratic_nonuniformity_discrepancy_partition_explicit alpha hα hαone N
      ((quadraticDensityThreshold_le_exp_power hα hαone).trans hN)
      f (relativeBalanced_discValued A S delta hAS hδ hδone) hnot
  obtain ⟨K, R, hR, _, hRproper, hcount, hdiam, hnorm⟩ :=
    small_diameter_partition_refinement Q (beta / 64) (by positivity) hQ hQproper
  have hdisR : beta * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := hdis.trans (hnorm f)
  obtain ⟨j, hsub, hsize, hinc⟩ := interval_small_diameter_relative_increment R hL A delta beta
    hAS hδ hδone hβ hcard hR hdiam hscale hdisR
  have hM : 0 < M := section18_partition_index_nonempty (fun i ↦ (Q i).carrier) hQ
  have hK : 0 < K := section18_partition_index_nonempty (fun i ↦ (R i).carrier) hR
  have hMbound : (M : Real) ≤ (N : Real) ^ (1 - sigma) := by
    rw [hQ.averageCellSize_univ] at havg
    have hm := (le_div_iff₀ (show (0 : Real) < M by exact_mod_cast hM)).mp havg
    rw [Real.rpow_sub hNr, Real.rpow_one]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNr sigma)).2
    simpa only [mul_comm] using hm
  have hcount' : (K : Real) ≤ C * (N : Real) ^ (1 - sigma / 16) := by
    calc
      _ ≤ C * (M : Real) ^ (1 / 16 : Real) * (N : Real) ^ (15 / 16 : Real) := hcount
      _ ≤ C * ((N : Real) ^ (1 - sigma)) ^ (1 / 16 : Real) * (N : Real) ^ (15 / 16 : Real) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hMbound (by norm_num)) hC.le)
          (Real.rpow_nonneg hNr.le _)
      _ = _ := by
        rw [← Real.rpow_mul hNr.le, mul_assoc, ← Real.rpow_add hNr]
        congr 2
        ring
  have hsize' : beta / (8 * C) * (N : Real) ^ (sigma / 16) ≤ beta * N / (8 * K) := by
    apply (le_div_iff₀ (show (0 : Real) < 8 * K by positivity)).2
    have hp : (N : Real) ^ (sigma / 16) * (N : Real) ^ (1 - sigma / 16) = N := by
      rw [← Real.rpow_add hNr, show sigma / 16 + (1 - sigma / 16) = 1 by ring, Real.rpow_one]
    calc
      _ = (beta / C * (N : Real) ^ (sigma / 16)) * K := by ring
      _ ≤ (beta / C * (N : Real) ^ (sigma / 16)) * (C * (N : Real) ^ (1 - sigma / 16)) :=
        mul_le_mul_of_nonneg_left hcount' (by positivity)
      _ = beta * ((N : Real) ^ (sigma / 16) * (N : Real) ^ (1 - sigma / 16)) := by field_simp
      _ = _ := by rw [hp]
  exact ⟨R j, hRproper j, hsub, hsize'.trans hsize, hinc⟩

end LeanProofs.GowersSzemeredi
