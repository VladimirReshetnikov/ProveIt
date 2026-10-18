import GowersSzemeredi.Proofs18IntervalPartitionUnwrap
import GowersSzemeredi.Proofs18FunctionDiscrepancyReduction

/-! Full ordinary interval discrepancy partitions obtained from the function
inverse theorem. Wrapping cells are split, so no discrepancy is discarded. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- A fixed sixteenth-modulus diameter is short enough to unwrap whenever
N is at least four, including the rounding in an integer diameter bound. -/
theorem sixteenth_diameter_short {N : Nat} (hN : 4 ≤ N) :
    2 * (Nat.floor ((1 / 16 : Real) * N) + 1) < N := by
  have hn : (4 : Real) ≤ N := by exact_mod_cast hN
  have hf := Nat.floor_le (show (0 : Real) ≤ (1 / 16 : Real) * N by positivity)
  have hr : (2 : Real) * ((Nat.floor ((1 / 16 : Real) * N) : Real) + 1) < N := by linarith
  exact_mod_cast hr

/-- A function inverse bound yields a full partition of its supporting
integer interval. The cell count loses a factor two and a factor sixteen in
the exponent; the discrepancy lower bound is preserved exactly. -/
theorem FunctionDiscrepancyBound.full_interval_partition
    {degree N L : Nat} [NeZero N] [Fact N.Prime] {alpha beta sigma T : Real}
    (hbound : FunctionDiscrepancyBound degree alpha beta sigma T)
    (hN : 4 ≤ N) (hL : L ≤ N) (hT : T ≤ N)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (hsupp : ∀ x, L ≤ x.val → f x = 0) (hnot : ¬ UniformOfDegree f alpha degree) :
    ∃ J : Nat, ∃ R : Fin J → NatAP,
      IsNatAPPartition R (Finset.range L) ∧ (∀ j, (R j).IsProper) ∧
      (J : Real) ≤ 2 * boundaryRefinementConstant (1 / 16) * (N : Real) ^ (1 - sigma / 16) ∧
      beta * N ≤ ∑ j, ‖∑ t ∈ (R j).carrier, f (t : ZMod N)‖ := by
  obtain ⟨M, Q, hQ, hQproper, havg, hdis⟩ := hbound N hT f hf hnot
  obtain ⟨K, S, hS, _, hSproper, hcount, hdiam, hnorm⟩ :=
    small_diameter_partition_refinement Q (1 / 16) (by norm_num) hQ hQproper
  have hdiamNat (i : Fin K) : diameterAtMost (S i).carrier (Nat.floor ((1 / 16 : Real) * N)) := by
    obtain ⟨d, ⟨a, ha⟩, hdb⟩ := hdiam i
    refine ⟨a, ha.trans fun x hx => ?_⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr
      ⟨Fin.castLE (Nat.succ_le_succ (Nat.le_floor hdb)) j, Finset.mem_univ _, hj⟩
  obtain ⟨J, R, hJ, hR, hRproper, htransport⟩ := small_diameter_partition_interval_unwrap
    S hS hSproper hL hdiamNat (sixteenth_diameter_short hN)
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hC : 0 < boundaryRefinementConstant (1 / 16) := section5LocalRefinementConstant_pos _ _
  rw [hQ.averageCellSize_univ,
    le_div_iff₀' (Nat.cast_pos.mpr (section18_partition_index_nonempty _ hQ))] at havg
  have hKbound : (K : Real) ≤ boundaryRefinementConstant (1 / 16) * N ^ (1 - sigma / 16) := by
    refine hcount.trans ?_
    rw [show 1 - sigma / 16 = (1 - sigma) * (1 / 16) + 15 / 16 by ring, Real.rpow_add hNr,
      Real.rpow_mul hNr.le, ← mul_assoc]
    gcongr
    rw [Real.rpow_sub hNr, Real.rpow_one, le_div_iff₀ (by positivity)]
    exact havg
  refine ⟨J, R, hR, hRproper, ?_, (hdis.trans (hnorm f)).trans (htransport f hsupp)⟩
  rw [hJ, Nat.cast_mul, Nat.cast_ofNat]
  linarith

end LeanProofs.GowersSzemeredi
