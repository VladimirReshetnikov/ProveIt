import GowersSzemeredi.Proofs18QuadraticDiscrepancy
import GowersSzemeredi.Proofs18QuantitativeSzemeredi

/-! An unconditional quadratic density increment. The size exponent and
density gain are explicit; the sufficiently-large threshold is existential. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Balanced indicator functions take values in the complex unit disc. -/
theorem balanced_discValued {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    DiscValued (balanced A) := by
  intro x
  rw [section18_balanced_eq_real, Complex.norm_real, Real.norm_eq_abs]
  exact section18_balancedReal_abs_le_one A x

/-- A proper discrepancy partition gives a density increment proportional
to its total discrepancy on a cell proportional to its average size. -/
theorem density_increment_of_discrepancy_partition {N M : Nat} [NeZero N]
    (A : Finset (ZMod N)) (P : Fin M → ModAP N) (beta s : Real)
    (hβ : 0 ≤ beta)
    (hpart : IsPartition (fun i ↦ (P i).carrier) Finset.univ)
    (havg : s ≤ averageCellSize (fun i ↦ (P i).carrier))
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (P i).carrier, balanced A x‖) :
    ∃ j : Fin M, beta / 4 * s ≤ ((P j).carrier.card : Real) ∧
      (density A + beta / 4) * (P j).carrier.card ≤ (A ∩ (P j).carrier).card := by
  have hM := section18_partition_index_nonempty (fun i ↦ (P i).carrier) hpart
  have hdisReal : beta * N ≤ ∑ i, |∑ x ∈ (P i).carrier, section18BalancedReal A x| := by
    simpa only [section18_balanced_eq_real, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using hdis
  obtain ⟨j, hinc, hsize⟩ := lemma_5_15_holds N M (section18BalancedReal A)
    (fun i ↦ (P i).carrier) beta hM hβ (section18_balancedReal_abs_le_one A)
    (section18_balancedReal_sum_zero A) hpart hdisReal
  refine ⟨j, ?_, ?_⟩
  · calc
      beta / 4 * s ≤ beta / 4 * averageCellSize (fun i ↦ (P i).carrier) :=
        mul_le_mul_of_nonneg_left havg (by positivity)
      _ = beta * N / (4 * M) := by rw [hpart.averageCellSize_univ]; ring
      _ ≤ _ := hsize
  · rw [section18_balancedReal_sum_inter] at hinc
    nlinarith only [hinc]

/-- Failure of quadratic uniformity of a balanced set yields a genuine
positive density increment on a long proper progression. This theorem uses
no unproved inverse theorem or assumed Section 18 induction. -/
theorem quadratic_nonuniformity_density_increment :
    ∀ alpha : Real, 0 < alpha → alpha ≤ 1 → ∃ N₀ : Nat,
      ∀ (N : Nat) [NeZero N] [Fact N.Prime], N₀ ≤ N →
        ∀ A : Finset (ZMod N), ¬ UniformSetOfDegree A alpha 2 →
        ∃ P : ModAP N, P.IsProper ∧
          quadraticDiscrepancyParameter alpha / 4 *
            (N : Real) ^ quadraticDiscrepancyExponent alpha ≤ (P.carrier.card : Real) ∧
          (density A + quadraticDiscrepancyParameter alpha / 4) * P.carrier.card ≤
            (A ∩ P.carrier).card := by
  intro alpha hα hαone
  obtain ⟨N₀, hN₀⟩ := quadratic_nonuniformity_discrepancy_partition alpha hα hαone
  refine ⟨N₀, fun N _ _ hN A hnot ↦ ?_⟩
  obtain ⟨M, P, hpart, hproper, havg, hdis⟩ := hN₀ N hN (balanced A) (balanced_discValued A) hnot
  have hβ : 0 ≤ quadraticDiscrepancyParameter alpha := by
    unfold quadraticDiscrepancyParameter
    positivity
  obtain ⟨j, hsize, hinc⟩ := density_increment_of_discrepancy_partition A P _ _ hβ hpart havg hdis
  exact ⟨P j, hproper j, hsize, hinc⟩

end LeanProofs.GowersSzemeredi
