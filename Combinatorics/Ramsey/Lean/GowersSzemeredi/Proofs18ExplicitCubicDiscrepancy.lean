import GowersSzemeredi.Proofs18CubicDiscrepancy
import GowersSzemeredi.Proofs18ExplicitCubicTwistedDiscrepancy

/-! A fully explicit threshold for the cubic function inverse theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

def cubicInverseThreshold (alpha : Real) : Real :=
  max (cubicTwistedThreshold alpha)
    (positivePowerThreshold (cubicPhaseRefinementConstant alpha) 1
      (cubicDiscrepancyExponent alpha))

/-- Every disc-valued function failing cubic uniformity has an untwisted
proper discrepancy partition, with explicit positive discrepancy and average
size parameters and an explicit modulus threshold. -/
theorem cubic_nonuniformity_discrepancy_partition_explicit (alpha : Real)
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], cubicInverseThreshold alpha ≤ (N : Real) →
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
  intro N _ _ hN f hf hnot
  obtain ⟨phi, l, K, Q, hpoly, hlength, hQ, _, hcount, hdis⟩ :=
    cubic_nonuniformity_twisted_discrepancy_explicit alpha hα hαone N
      ((le_max_left _ _).trans hN) f hf hnot
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
    simpa only [one_mul] using
      positivePowerThreshold_spec (C := C) zero_lt_one hs ((le_max_right _ _).trans hN)
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

/-- The cubic inverse interface with every threshold specified by a finite formula. -/
theorem cubic_function_discrepancy_bound_explicit {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    FunctionDiscrepancyBound 3 alpha (cubicDiscrepancyParameter alpha)
      (cubicDiscrepancyExponent alpha) (cubicInverseThreshold alpha) := by
  intro N _ _ hN f hf hnot
  exact cubic_nonuniformity_discrepancy_partition_explicit alpha hα hαone N hN f hf hnot

end LeanProofs.GowersSzemeredi
