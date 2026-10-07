import GowersSzemeredi.Proofs05CoverMass

/-! Weighted phase removal and transfer to a positive-density cell. The error
is multiplied by the actual balanced mass, preserving the high-correlation
budget of the threshold-free argument for Corollary 5.8. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem weighted_phase_removal_cell {X : Type*} (S : Finset X)
    (f w : X → Complex) (z : Complex) (hz : ‖z‖ = 1) :
    ‖∑ x ∈ S, f x * w x‖ ≤
      ‖∑ x ∈ S, f x‖ + ∑ x ∈ S, ‖f x‖ * ‖w x - z‖ := by
  have heq : (∑ x ∈ S, f x * w x) =
      (∑ x ∈ S, f x) * z + ∑ x ∈ S, f x * (w x - z) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq]
  calc
    _ ≤ ‖(∑ x ∈ S, f x) * z‖ + ‖∑ x ∈ S, f x * (w x - z)‖ := norm_add_le _ _
    _ ≤ ‖∑ x ∈ S, f x‖ + ∑ x ∈ S, ‖f x‖ * ‖w x - z‖ := by
      rw [norm_mul, hz, mul_one]
      have h := norm_sum_le S (fun x => f x * (w x - z))
      simp only [norm_mul] at h
      linarith

theorem weighted_phase_removal_partition {X : Type*} [DecidableEq X] {m : Nat}
    (P : Fin m → Finset X) (U : Finset X) (hP : IsPartition P U)
    (f w : X → Complex) (z : Fin m → Complex) (hz : ∀ i, ‖z i‖ = 1) :
    ‖∑ x ∈ U, f x * w x‖ ≤ (∑ i, ‖∑ x ∈ P i, f x‖) +
      ∑ i, ∑ x ∈ P i, ‖f x‖ * ‖w x - z i‖ := by
  rw [← hP.sum_values (fun x => f x * w x)]
  calc
    _ ≤ ∑ i, ‖∑ x ∈ P i, f x * w x‖ := norm_sum_le _ _
    _ ≤ ∑ i, (‖∑ x ∈ P i, f x‖ + ∑ x ∈ P i, ‖f x‖ * ‖w x - z i‖) :=
      Finset.sum_le_sum fun i _ => weighted_phase_removal_cell (P i) f w (z i) (hz i)
    _ = _ := Finset.sum_add_distrib

theorem weighted_phase_removal_uniform {X : Type*} [DecidableEq X] {m : Nat}
    (P : Fin m → Finset X) (U : Finset X) (hP : IsPartition P U)
    (f w : X → Complex) (z : Fin m → Complex) (hz : ∀ i, ‖z i‖ = 1)
    {epsilon : Real} (he : ∀ i x, x ∈ P i → ‖w x - z i‖ ≤ epsilon) :
    ‖∑ x ∈ U, f x * w x‖ ≤ (∑ i, ‖∑ x ∈ P i, f x‖) +
      epsilon * ∑ x ∈ U, ‖f x‖ := by
  apply (weighted_phase_removal_partition P U hP f w z hz).trans
  have herror : (∑ i, ∑ x ∈ P i, ‖f x‖ * ‖w x - z i‖) ≤
      epsilon * ∑ x ∈ U, ‖f x‖ := by
    calc
      _ ≤ ∑ i, ∑ x ∈ P i, epsilon * ‖f x‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro x hx
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (he i x hx) (norm_nonneg (f x))
      _ = _ := by simp only [← Finset.mul_sum, hP.sum_values]
  linarith

theorem sum_realSetBalanced_on {N : Nat} [NeZero N] (A U : Finset (ZMod N)) :
    (∑ x ∈ U, realSetBalanced A x) = (A ∩ U).card - density A * U.card := by
  simp only [realSetBalanced, Finset.sum_sub_distrib, sum_realSetIndicator_on,
    Finset.sum_const, nsmul_eq_mul]
  ring

theorem sum_realSetBalanced_cover_nonneg {N : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (hAU : A ⊆ U) :
    0 ≤ ∑ x ∈ U, realSetBalanced A x := by
  have hcard : (A.card : Real) = density A * N :=
    (div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne N)).symm
  have hU : (U.card : Real) ≤ N := by
    exact_mod_cast (show U.card ≤ N by simpa only [ZMod.card] using U.card_le_univ)
  rw [sum_realSetBalanced_on, Finset.inter_eq_left.mpr hAU, hcard]
  exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hU (density_nonneg A))

theorem cover_discrepancy_positive_cell {N m : Nat} [NeZero N]
    (A U : Finset (ZMod N)) (P : Fin m → Finset (ZMod N))
    (hP : IsPartition P U) (hAU : A ⊆ U) (hcell : ∀ i, 0 < (P i).card)
    {beta : Real} (hb : 0 < beta)
    (hdis : 2 * beta * N ≤ ∑ i, ‖∑ x ∈ P i, balanced A x‖) :
    ∃ i, (density A + beta) * (P i).card ≤ (A ∩ P i).card := by
  classical
  let g : Fin m → Real := fun i => ∑ x ∈ P i, realSetBalanced A x
  have hnorm (i : Fin m) : ‖∑ x ∈ P i, balanced A x‖ = |g i| := by
    simp only [balanced_eq_realSetBalanced, ← Complex.ofReal_sum, Complex.norm_real,
      Real.norm_eq_abs, g]
  have hsigned : 0 ≤ ∑ i, g i := by
    rw [show (∑ i, g i) = ∑ x ∈ U, realSetBalanced A x from hP.sum_values _]
    exact sum_realSetBalanced_cover_nonneg A U hAU
  have habs (x : Real) : |x| = 2 * max x 0 - x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, max_eq_left hx]; ring
    · rw [abs_of_nonpos hx, max_eq_right hx]; ring
  simp only [hnorm, habs, Finset.sum_sub_distrib, ← Finset.mul_sum] at hdis
  have hpositive : beta * N ≤ ∑ i, max (g i) 0 := by linarith
  have hU : (U.card : Real) ≤ N := by
    exact_mod_cast (show U.card ≤ N by simpa only [ZMod.card] using U.card_le_univ)
  have hcards : (∑ i, ((P i).card : Real)) = U.card := by exact_mod_cast hP.sum_card
  have hweighted : (∑ i, beta * (P i).card) ≤ ∑ i, max (g i) 0 := by
    rw [← Finset.mul_sum, hcards]
    exact (mul_le_mul_of_nonneg_left hU hb.le).trans hpositive
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra hno
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hno
    rw [hempty, Finset.sum_empty] at hpositive
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    exact (not_le_of_gt (mul_pos hb hN)) hpositive
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le hnonempty hweighted
  have hpos : 0 < beta * (P i).card := mul_pos hb (by exact_mod_cast hcell i)
  have hgi : 0 < g i := by
    by_contra hno
    rw [max_eq_right (le_of_not_gt hno)] at hi
    linarith
  rw [max_eq_left hgi.le] at hi
  have hformula := sum_realSetBalanced_on A (P i)
  change g i = _ at hformula
  refine ⟨i, ?_⟩
  linarith

end LeanProofs.GowersSzemeredi
