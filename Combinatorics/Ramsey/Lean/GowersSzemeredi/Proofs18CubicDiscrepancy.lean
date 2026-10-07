import GowersSzemeredi.Proofs18CubicTwistedDiscrepancy

/-! An unconditional function discrepancy theorem in degree three, obtained
from the constructed Section 13 inverse theorem and complete local transport.
The exponent is explicit; the original modulus threshold remains qualitative. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def cubicDiscrepancyExponent (alpha : Real) : Real :=
  cubicLocalizationExponent alpha * cubicLocalCountExponent alpha /
    (2 * (polynomialPartitionConstant 3 : Real))

def cubicDiscrepancyParameter (alpha : Real) : Real :=
  cubicTwistedDiscrepancyParameter alpha / 2

def cubicTwistedCountConstant (alpha : Real) : Real :=
  cubicLocalCountConstant alpha * (12 : Real) ^ cubicLocalCountExponent alpha

def cubicPhaseRefinementConstant (alpha : Real) : Real :=
  section5LocalRefinementConstant 3 (cubicTwistedDiscrepancyParameter alpha) *
    (cubicTwistedCountConstant alpha) ^ (polynomialPartitionConstant 3 : Real)⁻¹

theorem cubicDiscrepancyExponent_pos {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < cubicDiscrepancyExponent alpha := by
  have ht := (cubicLocalCountExponent_bounds hα hαone).1
  unfold cubicDiscrepancyExponent cubicLocalizationExponent polynomialPartitionConstant
  positivity

theorem cubicDiscrepancyParameter_pos {alpha : Real} (hα : 0 < alpha) :
    0 < cubicDiscrepancyParameter alpha := by
  have ha := cubicLocalQuadraticParameter_pos hα
  unfold cubicDiscrepancyParameter cubicTwistedDiscrepancyParameter
    cubicLocalizedMassParameter quadraticDiscrepancyParameter
  positivity

/-- Convert the common-cell-length count to a power of the old modulus. -/
theorem cubic_twisted_count_power {alpha : Real} (hα : 0 < alpha) (hαone : alpha ≤ 1)
    {N l J : Nat} [NeZero N]
    (hl : (N : Real) ^ cubicLocalizationExponent alpha / 12 ≤ l)
    (hcount : (J : Real) ≤ cubicLocalCountConstant alpha * N / (l : Real) ^ cubicLocalCountExponent alpha) :
    (J : Real) ≤ cubicTwistedCountConstant alpha *
      (N : Real) ^ (1 - cubicLocalizationExponent alpha * cubicLocalCountExponent alpha) := by
  let e := cubicLocalizationExponent alpha
  let t := cubicLocalCountExponent alpha
  let D := cubicLocalCountConstant alpha
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have ht : 0 < t := (cubicLocalCountExponent_bounds hα hαone).1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbase : 0 < (N : Real) ^ e / 12 := by positivity
  have hpow := Real.rpow_le_rpow hbase.le hl ht.le
  calc
    (J : Real) ≤ D * N / (l : Real) ^ t := hcount
    _ ≤ D * N / ((N : Real) ^ e / 12) ^ t :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hbase t) hpow
    _ = cubicTwistedCountConstant alpha * (N : Real) ^ (1 - e * t) := by
      rw [Real.div_rpow (Real.rpow_nonneg hN.le _) (by norm_num : (0 : Real) ≤ 12),
        ← Real.rpow_mul hN.le, Real.rpow_sub hN, Real.rpow_one]
      change D * N / ((N : Real) ^ (e * t) / (12 : Real) ^ t) =
        (D * (12 : Real) ^ t) * ((N : Real) / (N : Real) ^ (e * t))
      field_simp

/-- Every disc-valued function failing cubic uniformity has an untwisted
proper discrepancy partition, with explicit positive discrepancy and average
size parameters. The sufficiently-large threshold depends only on alpha. -/
theorem cubic_nonuniformity_discrepancy_partition (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) : ∃ N₀ : Nat,
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha 3 →
      ∃ J : Nat, ∃ R : Fin J → ModAP N,
        IsPartition (fun j => (R j).carrier) Finset.univ ∧
        (∀ j, (R j).IsProper) ∧
        (N : Real) ^ cubicDiscrepancyExponent alpha ≤ averageCellSize (fun j => (R j).carrier) ∧
        cubicDiscrepancyParameter alpha * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  let e := cubicLocalizationExponent alpha * cubicLocalCountExponent alpha
  let q : Real := (polynomialPartitionConstant 3 : Real)⁻¹
  let beta := cubicTwistedDiscrepancyParameter alpha
  let D := cubicTwistedCountConstant alpha
  let C := cubicPhaseRefinementConstant alpha
  let s := cubicDiscrepancyExponent alpha
  have hs : 0 < s := cubicDiscrepancyExponent_pos hα hαone
  have hq : 0 < q := by dsimp [q, polynomialPartitionConstant]; positivity
  have hβ : 0 < beta := by
    have h := cubicDiscrepancyParameter_pos hα
    change 0 < beta / 2 at h
    linarith
  have hD : 0 < D := by
    have h := lt_of_lt_of_le zero_lt_one (le_max_left (1 : Real)
      (2 * boundaryRefinementConstant (1 / 16) * (8 : Real) ^ (1 - cubicLocalCountExponent alpha)))
    dsimp [D, cubicTwistedCountConstant, cubicLocalCountConstant]
    positivity
  have heq : s = e * q / 2 := by dsimp [s, e, q, cubicDiscrepancyExponent]; ring
  obtain ⟨N₁, hN₁⟩ := cubic_nonuniformity_twisted_discrepancy alpha hα hαone
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (eventually_nat_mul_rpow_le (C := C) (D := 1) hs zero_lt_one)
  refine ⟨max N₁ N₂, fun N _ _ hN f hf hnot => ?_⟩
  obtain ⟨phi, l, K, Q, hpoly, hlength, hQ, _, hcount, hdis⟩ := hN₁ N (by omega) f hf hnot
  have hcount' : (K : Real) ≤ D * (N : Real) ^ (1 - e) :=
    cubic_twisted_count_power hα hαone hlength hcount
  obtain ⟨J, R, hR, _, hRproper, hJ, hdisR⟩ := variable_polynomial_phase_refinement
    Q (fun _ => phi) f beta (by omega) hβ (fun _ => hpoly) hf hQ hdis
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hJ' : (J : Real) ≤ C * (N : Real) ^ (1 - e * q) := by
    calc
      _ ≤ section5LocalRefinementConstant 3 beta * (K : Real) ^ q * (N : Real) ^ (1 - q) := hJ
      _ ≤ section5LocalRefinementConstant 3 beta * (D * (N : Real) ^ (1 - e)) ^ q * (N : Real) ^ (1 - q) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hcount' hq.le)
            (section5LocalRefinementConstant_pos _ _).le) (Real.rpow_nonneg hNr.le _)
      _ = _ := by
        rw [Real.mul_rpow hD.le (Real.rpow_nonneg hNr.le _), ← Real.rpow_mul hNr.le]
        have hp : (N : Real) ^ ((1 - e) * q) * (N : Real) ^ (1 - q) = (N : Real) ^ (1 - e * q) := by
          rw [← Real.rpow_add hNr]
          congr 1
          ring
        change (section5LocalRefinementConstant 3 beta * (D ^ q * (N : Real) ^ ((1 - e) * q))) *
          (N : Real) ^ (1 - q) = (section5LocalRefinementConstant 3 beta * D ^ q) * (N : Real) ^ (1 - e * q)
        rw [← hp]
        ring
  have hCbound : C ≤ (N : Real) ^ s := by
    simpa only [Real.rpow_zero, mul_one, one_mul] using hN₂ N (by omega)
  have hJbound : (J : Real) ≤ (N : Real) ^ (1 - s) := by
    calc
      _ ≤ C * (N : Real) ^ (1 - e * q) := hJ'
      _ ≤ (N : Real) ^ s * (N : Real) ^ (1 - e * q) :=
        mul_le_mul_of_nonneg_right hCbound (Real.rpow_nonneg hNr.le _)
      _ = _ := by rw [← Real.rpow_add hNr]; congr 1; linarith only [heq]
  have hJpos := section18_partition_index_nonempty (fun j => (R j).carrier) hR
  refine ⟨J, R, hR, hRproper, ?_, hdisR⟩
  rw [hR.averageCellSize_univ]
  apply (le_div_iff₀ (show (0 : Real) < J by exact_mod_cast hJpos)).2
  calc
    _ ≤ (N : Real) ^ s * (N : Real) ^ (1 - s) :=
      mul_le_mul_of_nonneg_left hJbound (Real.rpow_nonneg hNr.le _)
    _ = N := by rw [← Real.rpow_add hNr, show s + (1 - s) = 1 by ring, Real.rpow_one]

end LeanProofs.GowersSzemeredi
