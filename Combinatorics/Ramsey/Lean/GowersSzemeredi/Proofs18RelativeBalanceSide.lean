import GowersSzemeredi.Proofs18RelativeBalance
import GowersSzemeredi.Proofs05_10Side

/-! Declarations of `Proofs18RelativeBalance` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- A discrepancy partition yields an increment relative to the original
support, on its intersection with one cell. The intersection need not be an
arithmetic progression. Its mass retains a second factor of the increment. -/
theorem relative_density_increment_of_discrepancy_partition {N M : Nat} [NeZero N]
    (A S : Finset (ZMod N)) (delta beta s : Real) (P : Fin M → ModAP N)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hβ : 0 ≤ beta)
    (hcard : (A.card : Real) = delta * S.card)
    (hpart : IsPartition (fun i ↦ (P i).carrier) Finset.univ)
    (havg : s ≤ averageCellSize (fun i ↦ (P i).carrier))
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (P i).carrier, relativeBalanced A S delta x‖) :
    ∃ j : Fin M,
      beta / 4 * s ≤ ((P j).carrier.card : Real) ∧
      (beta / 4) ^ 2 * s ≤ ((S ∩ (P j).carrier).card : Real) ∧
      (delta + beta / 4) * (S ∩ (P j).carrier).card ≤ (A ∩ (P j).carrier).card := by
  have hM := section18_partition_index_nonempty (fun i ↦ (P i).carrier) hpart
  have hdisReal : beta * N ≤ ∑ i, |∑ x ∈ (P i).carrier, relativeBalancedReal A S delta x| := by
    simpa only [relativeBalanced, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using hdis
  obtain ⟨j, hinc, hsize⟩ := lemma_5_15_holds N M (relativeBalancedReal A S delta)
    (fun i ↦ (P i).carrier) beta hM hβ
    (relativeBalancedReal_abs_le_one A S delta hAS hδ hδone)
    (relativeBalancedReal_sum_zero A S delta hcard) hpart hdisReal
  have hPsize : beta / 4 * s ≤ ((P j).carrier.card : Real) := by
    calc
      _ ≤ beta / 4 * averageCellSize (fun i ↦ (P i).carrier) :=
        mul_le_mul_of_nonneg_left havg (by positivity)
      _ = beta * N / (4 * M) := by rw [hpart.averageCellSize_univ]; ring
      _ ≤ _ := hsize
  rw [relativeBalancedReal_sum] at hinc
  have hsub : ((A ∩ (P j).carrier).card : Real) ≤ (S ∩ (P j).carrier).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right hAS)
  have hcap : ((S ∩ (P j).carrier).card : Real) ≤ (P j).carrier.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hmass : beta / 4 * ((P j).carrier.card : Real) ≤ (S ∩ (P j).carrier).card := by
    have hnonneg : 0 ≤ delta * ((S ∩ (P j).carrier).card : Real) := by positivity
    nlinarith only [hinc, hsub, hnonneg]
  refine ⟨j, hPsize, ?_, ?_⟩
  · have hm := mul_le_mul_of_nonneg_left hPsize (by positivity : 0 ≤ beta / 4)
    nlinarith only [hm, hmass]
  · have hm := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ beta / 4)
    nlinarith only [hinc, hm]

end LeanProofs.GowersSzemeredi
