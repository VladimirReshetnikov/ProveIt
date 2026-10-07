import GowersSzemeredi.Proofs18IntervalPartitionUnwrap
import GowersSzemeredi.Proofs18SupportedFunctionDiscrepancy

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
    obtain ⟨d, hd, hdb⟩ := hdiam i
    obtain ⟨a, ha⟩ := hd
    refine ⟨a, ha.trans ?_⟩
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
    have hjd : (j : Nat) < d + 1 := j.isLt
    apply Finset.mem_image.mpr
    exact ⟨⟨j, by change (j : Nat) < Nat.floor ((1 / 16 : Real) * N) + 1; have := Nat.le_floor hdb; omega⟩, Finset.mem_univ _, hj⟩
  obtain ⟨J, R, hJ, hR, hRproper, htransport⟩ := small_diameter_partition_interval_unwrap
    S hS hSproper hL hdiamNat (sixteenth_diameter_short hN)
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hM := section18_partition_index_nonempty (fun i => (Q i).carrier) hQ
  have hMbound : (M : Real) ≤ (N : Real) ^ (1 - sigma) := by
    rw [hQ.averageCellSize_univ] at havg
    have hm := (le_div_iff₀ (show (0 : Real) < M by exact_mod_cast hM)).mp havg
    rw [Real.rpow_sub hNr, Real.rpow_one]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hNr sigma)).2
    simpa only [mul_comm] using hm
  have hKbound : (K : Real) ≤ boundaryRefinementConstant (1 / 16) * (N : Real) ^ (1 - sigma / 16) := by
    calc
      _ ≤ boundaryRefinementConstant (1 / 16) * (M : Real) ^ (1 / 16 : Real) *
          (N : Real) ^ (15 / 16 : Real) := hcount
      _ ≤ boundaryRefinementConstant (1 / 16) *
          ((N : Real) ^ (1 - sigma)) ^ (1 / 16 : Real) * (N : Real) ^ (15 / 16 : Real) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hMbound (by norm_num))
            (section5LocalRefinementConstant_pos _ _).le) (Real.rpow_nonneg hNr.le _)
      _ = _ := by
        rw [← Real.rpow_mul hNr.le, mul_assoc, ← Real.rpow_add hNr]
        congr 2
        ring
  refine ⟨J, R, hR, hRproper, ?_, (hdis.trans (hnorm f)).trans (htransport f hsupp)⟩
  rw [hJ, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ ≤ 2 * (boundaryRefinementConstant (1 / 16) * (N : Real) ^ (1 - sigma / 16)) :=
      mul_le_mul_of_nonneg_left hKbound (by norm_num)
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
