import GowersSzemeredi.Proofs05CoverMass

/-! Comparable parent sizes in the high-correlation branch. The estimates
retain all finite cardinalities and do not assume that the parents cover
the ambient cyclic group. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem high_correlation_parent_scale {N M L : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (P : Fin M → Finset (ZMod N))
    (w : Fin M → ZMod N → Complex) (hP : IsPartition P U) (hAU : A ⊆ U)
    (hw : ∀ i x, ‖w i x‖ ≤ 1)
    (hcomp : ∀ i j, (P i).card ≤ 2 * (P j).card)
    {alpha : Real} (ha0 : 0 < alpha) (hL : 0 < L)
    (hcor : alpha * N ≤ ∑ i, ‖∑ x ∈ P i, balanced A x * w i x‖)
    (hhigh : 3 * (1 - density A) / (2 * L) < alpha) (j : Fin M) :
    3 * (N : Real) < 8 * L * M * (P j).card := by
  have hd := cover_correlation_density_strict A U P w hP hAU hw ha0 hcor
  have hb : 0 < 1 - density A := sub_pos.mpr hd.2
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hLr : (0 : Real) < L := by exact_mod_cast hL
  have hsize : (U.card : Real) ≤ 2 * M * (P j).card := by
    exact_mod_cast comparable_partition_card_bound P U hP hcomp j
  have hmass := (cover_correlation_density_bounds A U P w hP hAU hw hcor).2
  have hparent : alpha * N ≤ 4 * M * (P j).card * (1 - density A) := by
    have h := mul_le_mul_of_nonneg_right hsize hb.le
    nlinarith [h, hmass]
  have hhigh' := (div_lt_iff₀ (show (0 : Real) < 2 * L by positivity)).mp hhigh
  have hstrict := mul_lt_mul_of_pos_right hhigh' hN
  have hupper := mul_le_mul_of_nonneg_left hparent (show (0 : Real) ≤ 2 * L by positivity)
  apply (mul_lt_mul_iff_right₀ hb).mp
  nlinarith [hstrict, hupper]

theorem high_correlation_parent_card_pos {N M : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (P : Fin M → Finset (ZMod N))
    (w : Fin M → ZMod N → Complex) (hP : IsPartition P U) (hAU : A ⊆ U)
    (hw : ∀ i x, ‖w i x‖ ≤ 1)
    (hcomp : ∀ i j, (P i).card ≤ 2 * (P j).card)
    {alpha : Real} (ha0 : 0 < alpha)
    (hcor : alpha * N ≤ ∑ i, ‖∑ x ∈ P i, balanced A x * w i x‖) :
    ∀ j, 0 < (P j).card := by
  have hd := (cover_correlation_density_strict A U P w hP hAU hw ha0 hcor).1
  have hA : 0 < A.card := by
    have hcard : (A.card : Real) = density A * N :=
      (div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne N)).symm
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    exact_mod_cast (hcard.symm ▸ mul_pos hd hN)
  have hU : 0 < U.card := hA.trans_le (Finset.card_le_card hAU)
  intro j
  have hsize := comparable_partition_card_bound P U hP hcomp j
  by_contra hno
  have hz : (P j).card = 0 := by omega
  rw [hz, mul_zero] at hsize
  omega

end LeanProofs.GowersSzemeredi
