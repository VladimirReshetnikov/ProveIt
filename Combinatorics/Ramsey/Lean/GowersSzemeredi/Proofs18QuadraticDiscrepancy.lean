import GowersSzemeredi.Proofs18TwistedPartitionDiscrepancy
import GowersSzemeredi.Proofs17QuadraticLocalization

/-! An untwisted discrepancy partition from quadratic nonuniformity, with
an explicit positive power for its average cell size. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The average cell-size exponent after quadratic phase removal and
absorption of the fixed refinement constant. -/
def quadraticDiscrepancyExponent (alpha : Real) : Real :=
  cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 / 4096

/-- The surviving normalized total discrepancy. -/
def quadraticDiscrepancyParameter (alpha : Real) : Real :=
  (2 : Real) ^ (-(20 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat)

/-- Fixed count constant from quadratic polynomial refinement. -/
def quadraticRefinementConstant (alpha : Real) : Real :=
  section5LocalRefinementConstant 2
    ((2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat)) *
    (6 : Real) ^ (1 / 2048 : Real)

/-- Total size divided by the number of cells is the average of a partition. -/
theorem IsPartition.averageCellSize_univ {N M : Nat} [NeZero N]
    {Q : Fin M → Finset (ZMod N)} (hQ : IsPartition Q Finset.univ) :
    averageCellSize Q = (N : Real) / M := by
  have hs : ∑ i, (Q i).card = N := by simpa using hQ.sum_card
  simp only [averageCellSize, hs]

/-- The cell count of a partition is controlled by any common positive
lower bound on its cell cardinalities. -/
theorem IsPartition.card_mul_le {N M : Nat} [NeZero N]
    {Q : Fin M → Finset (ZMod N)} (hQ : IsPartition Q Finset.univ)
    (x : Real) (hx : ∀ i, x ≤ (Q i).card) : (M : Real) * x ≤ N := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) ↦ hx i)
  have hcards : ∑ i, (Q i).card = N := by simpa using hQ.sum_card
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Nat.cast_sum, hcards] using hs

/-- Quadratic nonuniformity supplies an untwisted proper progression
partition with explicit average length and total discrepancy. The two power
conditions account for rounding and the fixed refinement constant. -/
theorem quadratic_nonuniformity_discrepancy_partition_of_power_bounds :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 →
      ∀ (N : Nat) [NeZero N] [Fact N.Prime],
        4 ≤ (N : Real) ^ cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1 →
        quadraticRefinementConstant alpha ≤ (N : Real) ^ quadraticDiscrepancyExponent alpha →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 2 →
        ∃ L : Nat, ∃ R : Fin L → ModAP N,
          IsPartition (fun j ↦ (R j).carrier) Finset.univ ∧
          (∀ j, (R j).IsProper) ∧
          (N : Real) ^ quadraticDiscrepancyExponent alpha ≤
            averageCellSize (fun j ↦ (R j).carrier) ∧
          quadraticDiscrepancyParameter alpha * N ≤
            ∑ j, ‖∑ s ∈ (R j).carrier, f s‖ := by
  intro alpha hα hαone N _ _ hlarge hbudget f hf hnot
  set e := cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1
  let beta := (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat)
  obtain ⟨phi, M, l, Q, hpoly, hpart, hproper, hlength, _, hfail⟩ :=
    quadratic_nonuniformity_localized_phase_removal_of_power_bound alpha hα hαone N hlarge f hf hnot
  have hl (i : Fin M) : l ≤ (Q i).carrier.card ∧ (Q i).carrier.card ≤ l + 1 := by
    rw [(hproper i).1]; rcases (hproper i).2 with h | h <;> omega
  obtain ⟨L, R, hR, _, hRproper, hcount, hbias⟩ :=
    twisted_partition_nonuniformity_discrepancy Q phi f beta (by omega) (by positivity) hpoly hf
      hpart (fun i ↦ (hl i).2) hfail
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hS := section5LocalRefinementConstant_pos 2 beta
  have hK : (polynomialPartitionConstant 2 : Real)⁻¹ = 1 / 2048 := by
    norm_num [polynomialPartitionConstant, Nat.factorial]
  rw [hK] at hcount
  -- `M ≤ 6 N^(1-e)`, from the common cell length
  have hM : (M : Real) ≤ 6 * (N : Real) ^ (1 - e) := by
    have hsum := hpart.card_mul_le ((N : Real) ^ e / 6)
      fun i ↦ hlength.trans (by exact_mod_cast (hl i).1)
    rw [Real.rpow_sub hNpos, Real.rpow_one, ← mul_div_assoc,
      le_div_iff₀ (Real.rpow_pos_of_pos hNpos _)]
    nlinarith only [hsum]
  have hL : (0 : Real) < L := by
    obtain ⟨j, _⟩ := (hR.1 (0 : ZMod N)).mp (Finset.mem_univ _)
    exact_mod_cast Nat.zero_lt_of_lt j.isLt
  have hparam : quadraticDiscrepancyParameter alpha = beta / 2 := by
    dsimp [quadraticDiscrepancyParameter, beta]
    generalize (alpha / 2) ^ (12359 : Nat) = a
    norm_num
    ring
  refine ⟨L, R, hR, hRproper, ?_, by simpa only [hparam] using hbias⟩
  rw [hR.averageCellSize_univ, le_div_iff₀ hL]
  calc (N : Real) ^ quadraticDiscrepancyExponent alpha * L
      ≤ (N : Real) ^ (e / 4096) * (section5LocalRefinementConstant 2 beta *
        (6 * (N : Real) ^ (1 - e)) ^ (1 / 2048 : Real) * (N : Real) ^ (1 - 1 / 2048 : Real)) := by
        refine mul_le_mul_of_nonneg_left (hcount.trans ?_) (by positivity)
        gcongr
    _ = (N : Real) ^ (e / 4096) * (section5LocalRefinementConstant 2 beta * 6 ^ (1 / 2048 : Real)) *
        ((N : Real) ^ ((1 - e) * (1 / 2048)) * (N : Real) ^ (1 - 1 / 2048 : Real)) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
        ring
    _ ≤ (N : Real) ^ (e / 4096) * (N : Real) ^ (e / 4096) *
        ((N : Real) ^ ((1 - e) * (1 / 2048)) * (N : Real) ^ (1 - 1 / 2048 : Real)) := by
        gcongr; exact hbudget
    _ = N := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
        convert Real.rpow_one (N : Real) using 2
        ring

end LeanProofs.GowersSzemeredi
