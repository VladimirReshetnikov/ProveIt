import GowersSzemeredi.Proofs18SupportedBoundaryDiscrepancy
import GowersSzemeredi.Proofs18FunctionDiscrepancyReduction

/-! The function inverse interface produces interior discrepancy cells on
an index interval, with an explicit bound on the full refinement count. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Boundary refinement of an interval-supported function consumes an
explicit inverse theorem only at its stated threshold. No balancing or
zero-mean hypothesis is required. -/
theorem FunctionDiscrepancyBound.interval_supported_discrepancy
    {degree N L : Nat} [NeZero N] [Fact N.Prime] {alpha beta sigma T : Real}
    (hbound : FunctionDiscrepancyBound degree alpha beta sigma T)
    (hβ : 0 < beta) (hL : L ≤ N) (hT : T ≤ N) (hscale : 32 ≤ beta * N)
    (g : Fin L → Complex) (hf : DiscValued (intervalExtension N g))
    (hnot : ¬ UniformOfDegree (intervalExtension N g) alpha degree) :
    ∃ K : Nat, ∃ R : Fin K → ModAP N,
      IsPartition (fun j => (R j).carrier) Finset.univ ∧
      (∀ j, (R j).IsProper) ∧
      (K : Real) ≤ boundaryRefinementConstant (beta / 64) * (N : Real) ^ (1 - sigma / 16) ∧
      ∃ G : Finset (Fin K),
        (∀ j ∈ G, (R j).carrier ⊆ finiteIntervalImage N (Finset.univ : Finset (Fin L))) ∧
        (7 * beta / 8) * N ≤ ∑ j ∈ G, ‖∑ x ∈ (R j).carrier, intervalExtension N g x‖ := by
  obtain ⟨M, Q, hQ, hQproper, havg, hdis⟩ := hbound N hT (intervalExtension N g) hf hnot
  have hsupp (x : ZMod N) (hx : x ∉ finiteIntervalImage N (Finset.univ : Finset (Fin L))) :
      intervalExtension N g x = 0 := by
    have hx' : ¬ x.val < L := fun h => hx ((mem_finiteIntervalSupport hL x).mpr h)
    simp only [intervalExtension, dif_neg hx']
  obtain ⟨K, R, hR, _, hRproper, hcount, G, hG, hdisG⟩ :=
    interval_supported_discrepancy_refinement (intervalExtension N g) Q beta hL hf hsupp
      hβ hscale hQ hQproper hdis
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hM := section18_partition_index_nonempty (fun i => (Q i).carrier) hQ
  have hMbound : (M : Real) ≤ (N : Real) ^ (1 - sigma) := by
    rw [hQ.averageCellSize_univ] at havg
    have hm := (le_div_iff₀ (show (0 : Real) < M by exact_mod_cast hM)).mp havg
    rw [Real.rpow_sub hNr, Real.rpow_one]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNr sigma)).2
    simpa only [mul_comm] using hm
  refine ⟨K, R, hR, hRproper, ?_, G, hG, hdisG⟩
  calc
    _ ≤ boundaryRefinementConstant (beta / 64) * (M : Real) ^ (1 / 16 : Real) *
        (N : Real) ^ (15 / 16 : Real) := hcount
    _ ≤ boundaryRefinementConstant (beta / 64) *
        ((N : Real) ^ (1 - sigma)) ^ (1 / 16 : Real) * (N : Real) ^ (15 / 16 : Real) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hMbound (by norm_num))
          (section5LocalRefinementConstant_pos _ _).le) (Real.rpow_nonneg hNr.le _)
    _ = _ := by
      rw [← Real.rpow_mul hNr.le, mul_assoc, ← Real.rpow_add hNr]
      congr 2
      ring

end LeanProofs.GowersSzemeredi
