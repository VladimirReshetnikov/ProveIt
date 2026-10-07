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
  let e := cor711Exponent ((alpha / 2) ^ (12359 : Nat)) 1
  let beta := (2 : Real) ^ (-(19 : Int)) * alpha ^ 2 * (alpha / 2) ^ (12359 : Nat)
  let q : Real := 1 / 2048
  let C := section5LocalRefinementConstant 2 beta * (6 : Real) ^ q
  have he : 0 < e := (quadratic_frequency_exponent_bounds hα hαone).1
  have hβ : 0 < beta := by dsimp [beta]; positivity
  have hq : 0 < q := by norm_num [q]
  have hC : 0 < C := mul_pos (section5LocalRefinementConstant_pos 2 beta) (by positivity)
  have hK : (polynomialPartitionConstant 2 : Real)⁻¹ = q := by
    norm_num [polynomialPartitionConstant, q, Nat.factorial]
  obtain ⟨phi, M, l, Q, hpoly, hpart, hproper, hlength, _, hfail⟩ :=
    quadratic_nonuniformity_localized_phase_removal_of_power_bound alpha hα hαone N hlarge f hf hnot
  have hsize : ∀ i, (Q i).carrier.card ≤ l + 1 := by
    intro i
    rw [(hproper i).1]
    rcases (hproper i).2 with h | h <;> omega
  obtain ⟨L, R, hR, _, hRproper, hcount, hbias⟩ :=
    twisted_partition_nonuniformity_discrepancy Q phi f beta (by omega) hβ (by omega)
      hpoly hf hpart hsize hfail
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hMbound : (M : Real) ≤ 6 * (N : Real) ^ (1 - e) := by
    have hsum := hpart.card_mul_le ((N : Real) ^ e / 6) (fun i ↦ by
      rw [(hproper i).1]
      have hli : l ≤ (Q i).length := by rcases (hproper i).2 with h | h <;> omega
      exact hlength.trans (by exact_mod_cast hli))
    have hp : 0 < (N : Real) ^ e := Real.rpow_pos_of_pos hNpos _
    rw [Real.rpow_sub hNpos, Real.rpow_one, ← mul_div_assoc]
    apply (le_div_iff₀ hp).2
    nlinarith only [hsum]
  have hcount' : (L : Real) ≤ C * (N : Real) ^ (1 - e * q) := by
    rw [hK] at hcount
    calc
      _ ≤ section5LocalRefinementConstant 2 beta * (M : Real) ^ q *
          (N : Real) ^ (1 - q) := hcount
      _ ≤ section5LocalRefinementConstant 2 beta * (6 * (N : Real) ^ (1 - e)) ^ q *
          (N : Real) ^ (1 - q) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hMbound hq.le)
            (section5LocalRefinementConstant_pos 2 beta).le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : Real) ≤ 6) (Real.rpow_nonneg hNpos.le _),
          ← Real.rpow_mul hNpos.le]
        have hp : (N : Real) ^ ((1 - e) * q) * (N : Real) ^ (1 - q) =
            (N : Real) ^ (1 - e * q) := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
        calc
          _ = C * ((N : Real) ^ ((1 - e) * q) * (N : Real) ^ (1 - q)) := by
            dsimp only [C]
            ring
          _ = _ := by rw [hp]
  have hexp : quadraticDiscrepancyExponent alpha = e * q / 2 := by
    dsimp [quadraticDiscrepancyExponent, e, q]
    ring
  have hCbound : C ≤ (N : Real) ^ (e * q / 2) := by
    simpa only [hexp, quadraticRefinementConstant, C, beta, q] using hbudget
  have hLbound : (L : Real) ≤ (N : Real) ^ (1 - e * q / 2) := by
    calc
      _ ≤ C * (N : Real) ^ (1 - e * q) := hcount'
      _ ≤ (N : Real) ^ (e * q / 2) * (N : Real) ^ (1 - e * q) :=
        mul_le_mul_of_nonneg_right hCbound (Real.rpow_nonneg hNpos.le _)
      _ = _ := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
  have hL : 0 < L := by
    obtain ⟨j, _⟩ := (hR.1 (0 : ZMod N)).mp (Finset.mem_univ _)
    exact Nat.zero_lt_of_lt j.isLt
  have hparam : quadraticDiscrepancyParameter alpha = beta / 2 := by
    dsimp [quadraticDiscrepancyParameter, beta]
    generalize (alpha / 2) ^ (12359 : Nat) = a
    norm_num
    ring
  refine ⟨L, R, hR, hRproper, ?_, by simpa only [hparam] using hbias⟩
  rw [hR.averageCellSize_univ, hexp]
  apply (le_div_iff₀ (show (0 : Real) < L by exact_mod_cast hL)).2
  calc
    _ ≤ (N : Real) ^ (e * q / 2) * (N : Real) ^ (1 - e * q / 2) :=
      mul_le_mul_of_nonneg_left hLbound (Real.rpow_nonneg hNpos.le _)
    _ = N := by rw [← Real.rpow_add hNpos, show e * q / 2 + (1 - e * q / 2) = 1 by ring, Real.rpow_one]

/-- Quadratic nonuniformity supplies an untwisted proper progression
partition with explicit average length and total discrepancy. Only the
fixed-parameter sufficiently-large threshold remains existential. -/
theorem quadratic_nonuniformity_discrepancy_partition :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 2 →
        ∃ L : Nat, ∃ R : Fin L → ModAP N,
          IsPartition (fun j ↦ (R j).carrier) Finset.univ ∧
          (∀ j, (R j).IsProper) ∧
          (N : Real) ^ quadraticDiscrepancyExponent alpha ≤
            averageCellSize (fun j ↦ (R j).carrier) ∧
          quadraticDiscrepancyParameter alpha * N ≤
            ∑ j, ‖∑ s ∈ (R j).carrier, f s‖ := by
  intro alpha hα hαone
  have he := (quadratic_frequency_exponent_bounds hα hαone).1
  have hs : 0 < quadraticDiscrepancyExponent alpha := by
    exact div_pos he (by norm_num)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_nat_mul_rpow_le (C := 4) (D := 1) he zero_lt_one)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (eventually_nat_mul_rpow_le (C := quadraticRefinementConstant alpha) (D := 1) hs zero_lt_one)
  refine ⟨max N₁ N₂, fun N _ _ hN ↦ ?_⟩
  apply quadratic_nonuniformity_discrepancy_partition_of_power_bounds alpha hα hαone N
  · simpa only [Real.rpow_zero, mul_one, one_mul] using hN₁ N (by omega)
  · simpa only [Real.rpow_zero, mul_one, one_mul] using hN₂ N (by omega)

end LeanProofs.GowersSzemeredi
