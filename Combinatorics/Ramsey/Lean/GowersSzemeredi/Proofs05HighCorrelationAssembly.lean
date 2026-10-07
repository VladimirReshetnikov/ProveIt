import GowersSzemeredi.Proofs05WeightedPhaseTransfer
import GowersSzemeredi.Proofs05BoxTransport

/-! Assemble the high-correlation density increment from lossless local
phase partitions. The analytic localization input is explicit: no partition
threshold is inferred from the hypotheses of Corollary 5.8. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem density_cell_of_weighted_refinements {N M : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (P : Fin M → Finset (ZMod N))
    (hP : IsPartition P U) (hAU : A ⊆ U)
    (m : Fin M → Nat) (R : (i : Fin M) → Fin (m i) → Finset (ZMod N))
    (hR : ∀ i, IsPartition (R i) (P i)) (hcell : ∀ i j, 0 < (R i j).card)
    (w : Fin M → ZMod N → Complex) (z : (i : Fin M) → Fin (m i) → Complex)
    (hz : ∀ i j, ‖z i j‖ = 1) {alpha epsilon : Real} (ha : 0 < alpha)
    (he : ∀ i j x, x ∈ R i j → ‖w i x - z i j‖ ≤ epsilon)
    (hcor : alpha * N ≤ ∑ i, ‖∑ x ∈ P i, balanced A x * w i x‖)
    (herror : epsilon * (∑ x ∈ U, ‖balanced A x‖) ≤ alpha / 3 * N) :
    ∃ i j, (density A + alpha / 3) * (R i j).card ≤ (A ∩ R i j).card := by
  classical
  let e := section5NatFlattenEquiv m
  let Q : Fin (∑ i, m i) → Finset (ZMod N) := fun j => R (e.symm j).1 (e.symm j).2
  have hQ : IsPartition Q U := finsetPartition_flatten m P U R hP hR
  have hQcell (j : Fin (∑ i, m i)) : 0 < (Q j).card := hcell _ _
  have hsum : (∑ j, ‖∑ x ∈ Q j, balanced A x‖) =
      ∑ i, ∑ j, ‖∑ x ∈ R i j, balanced A x‖ := by
    change (∑ j, (fun p : Σ i, Fin (m i) => ‖∑ x ∈ R p.1 p.2, balanced A x‖) (e.symm j)) = _
    calc
      _ = ∑ p : Σ i, Fin (m i), ‖∑ x ∈ R p.1 p.2, balanced A x‖ :=
        Equiv.sum_comp e.symm (fun p => ‖∑ x ∈ R p.1 p.2, balanced A x‖)
      _ = _ := Fintype.sum_sigma _
  have hbound : (∑ i, ‖∑ x ∈ P i, balanced A x * w i x‖) ≤
      (∑ i, ∑ j, ‖∑ x ∈ R i j, balanced A x‖) +
        epsilon * (∑ x ∈ U, ‖balanced A x‖) := by
    calc
      _ ≤ ∑ i, ((∑ j, ‖∑ x ∈ R i j, balanced A x‖) +
          epsilon * (∑ x ∈ P i, ‖balanced A x‖)) :=
        Finset.sum_le_sum fun i _ => weighted_phase_removal_uniform
          (R i) (P i) (hR i) (balanced A) (w i) (z i) (hz i) (he i)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hP.sum_values]
  have hdis : 2 * (alpha / 3) * N ≤ ∑ j, ‖∑ x ∈ Q j, balanced A x‖ := by
    rw [hsum]
    linarith
  obtain ⟨j, hj⟩ := cover_discrepancy_positive_cell A U Q hQ hAU hQcell (by positivity) hdis
  exact ⟨(e.symm j).1, (e.symm j).2, hj⟩

/-- In the high-correlation regime, phase error `1/(4L)` is paid for by the
balanced mass. All remaining assumptions describe the local partitions. -/
theorem density_cell_of_high_correlation {N M L : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (P : Fin M → Finset (ZMod N))
    (hP : IsPartition P U) (hAU : A ⊆ U) (hL : 0 < L)
    (m : Fin M → Nat) (R : (i : Fin M) → Fin (m i) → Finset (ZMod N))
    (hR : ∀ i, IsPartition (R i) (P i)) (hcell : ∀ i j, 0 < (R i j).card)
    (w : Fin M → ZMod N → Complex) (z : (i : Fin M) → Fin (m i) → Complex)
    (hz : ∀ i j, ‖z i j‖ = 1) {alpha : Real} (ha : 0 < alpha)
    (he : ∀ i j x, x ∈ R i j → ‖w i x - z i j‖ ≤ 1 / (4 * L))
    (hcor : alpha * N ≤ ∑ i, ‖∑ x ∈ P i, balanced A x * w i x‖)
    (hhigh : 3 * (1 - density A) / (2 * L) ≤ alpha) :
    ∃ i j, (density A + alpha / 3) * (R i j).card ≤ (A ∩ R i j).card := by
  have hLr : (0 : Real) < L := by exact_mod_cast hL
  have hd := density_nonneg A
  have hd1 := density_le_one A
  have hN : (0 : Real) ≤ N := by positivity
  apply density_cell_of_weighted_refinements A U P hP hAU m R hR hcell w z hz ha he hcor
  have hmass : (∑ x ∈ U, ‖balanced A x‖) ≤ 2 * (1 - density A) * N := by
    apply (sum_norm_balanced_cover_bounds A U hAU).1.trans
    have h := mul_le_mul_of_nonneg_right hd1
      (mul_nonneg (sub_nonneg.mpr hd1) hN)
    nlinarith
  calc
    _ ≤ (1 / (4 * L)) * (2 * (1 - density A) * N) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = ((1 - density A) / (2 * L)) * N := by ring
    _ ≤ alpha / 3 * N := by
      apply mul_le_mul_of_nonneg_right _ hN
      rw [mul_div_assoc] at hhigh
      linarith

end LeanProofs.GowersSzemeredi
