import GowersSzemeredi.Proofs10Error

/-!
# The averaging selection in Gowers's Section 10

This module proves Lemma 10.3 from the counting bounds of Lemma 10.1 and the
weighted error estimate of Lemma 10.2.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- The points lying in fibres smaller than the threshold used in Lemma 10.3
occupy at most half of `alpha ^ 2 * M * N` points. -/
private lemma small_anchor_fibre_card_bound {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real) (M : Nat) :
    (countWhere (fun x : X =>
      ¬ alpha ^ 2 * M / 2 ≤ (D.fibreSize x : Real)) : Real) ≤
        alpha ^ 2 * M * N / 2 :=
  (small_fibre_count_le D (T := alpha ^ 2 * M / 2) (by positivity)).trans_eq (by ring)

private lemma weightedError_nonneg {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N)) (x : X) :
    0 ≤ domainWeightedError D phi B x := by
  unfold domainWeightedError
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg
  · unfold domainProportionateError
    positivity
  · positivity

/-- **Gowers, Lemma 10.3.** -/
theorem lemma_10_3_holds : lemma_10_3 := by
  intro N _ X _ _ D phi B alpha M sigma eta hsetup hsigma
  obtain ⟨halpha, -, hM, hcard, -⟩ := hsetup.1
  let Q : X → Real := fun x => domainTotalWeight D x
  let E : X → Real := fun x => domainWeightedError D phi B x
  let A : Real := alpha ^ 4 * M ^ 4 * N ^ 3
  let C : Real := alpha ^ 3 * M ^ 3 * N ^ 2
  let S₁ : Finset X := Finset.univ.filter fun x => alpha ^ 2 * M / 2 ≤ (D.fibreSize x : Real)
  let S : Finset X := S₁.filter fun x => C / 4 ≤ Q x
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hA : 0 < A := by positivity
  have hbasic := lemma_10_1_holds N X D alpha M hsetup.1
  have hQT : A ≤ ∑ x, Q x := by simpa only [Q, domainTotalWeight, Nat.cast_sum] using hbasic.2.2
  -- the points in small fibres carry at most `A / 2`: each `Q x ≤ α²M³N²` by Lemma 10.1
  have hbad : (∑ x : X, if ¬ alpha ^ 2 * M / 2 ≤ (D.fibreSize x : Real) then Q x else 0) ≤
      A / 2 := by
    calc _ ≤ ∑ x : X, if ¬ alpha ^ 2 * M / 2 ≤ (D.fibreSize x : Real)
          then alpha ^ 2 * M ^ 3 * N ^ 2 else 0 :=
          Finset.sum_le_sum fun x _ => by split_ifs; exacts [le_rfl, hbasic.2.1 x]
      _ = (countWhere fun x : X => ¬ alpha ^ 2 * M / 2 ≤ (D.fibreSize x : Real)) *
          (alpha ^ 2 * M ^ 3 * N ^ 2) := by
          rw [countWhere_cast_eq_sum_ite, Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
      _ ≤ (alpha ^ 2 * M * N / 2) * (alpha ^ 2 * M ^ 3 * N ^ 2) := by
          gcongr; exact small_anchor_fibre_card_bound D alpha M
      _ = A / 2 := by dsimp only [A]; ring
  have hsplit₁ : ∑ x, Q x = ∑ x ∈ S₁, Q x +
      ∑ x : X, if ¬ alpha ^ 2 * M / 2 ≤ (D.fibreSize x : Real) then Q x else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_filter_add_sum_filter_not _ _ Q).symm
  -- the points of `S₁ \ S` carry at most `|X| C / 4 = A / 4`
  have hsmall : ∑ x ∈ S₁.filter (fun x => ¬ C / 4 ≤ Q x), Q x ≤ A / 4 := by
    calc _ ≤ ((S₁.filter fun x => ¬ C / 4 ≤ Q x).card : Real) * (C / 4) :=
          (Finset.sum_le_card_nsmul _ _ _ fun x hx =>
            (not_le.mp (Finset.mem_filter.mp hx).2).le).trans_eq (nsmul_eq_mul _ _)
      _ ≤ Fintype.card X * (C / 4) := by gcongr; exact Finset.card_le_univ _
      _ = A / 4 := by rw [hcard]; dsimp only [A, C]; ring
  have hsplit : ∑ x ∈ S, Q x + ∑ x ∈ S₁.filter (fun x => ¬ C / 4 ≤ Q x), Q x =
      ∑ x ∈ S₁, Q x := Finset.sum_filter_add_sum_filter_not S₁ _ Q
  -- so the anchors in `S` carry a quarter of the weight and, by Lemma 10.2, little error
  have hEtotal : ∑ x, E x ≤ 15 * eta * ∑ x, Q x := by
    simpa only [E, Q, domainWeightedError, domainTotalWeight, Nat.cast_sum] using
      lemma_10_2_holds N X D phi B alpha M sigma eta hsetup hsigma
  have hES : ∑ x ∈ S, E x ≤ ∑ x, E x := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ _) fun x _ _ => weightedError_nonneg D phi B x
  have hQS : ∑ x, Q x ≤ 4 * ∑ x ∈ S, Q x := by linarith
  obtain ⟨x, hxS, hx⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_of_sum_ne_zero (by linarith : (0 : Real) < ∑ x ∈ S, Q x).ne')
    (show ∑ x ∈ S, E x ≤ ∑ x ∈ S, 60 * eta * Q x by
      rw [← Finset.mul_sum]; linarith [mul_le_mul_of_nonneg_left hQS hsetup.2.2.1])
  obtain ⟨hx₁, hx₂⟩ := Finset.mem_filter.mp hxS
  exact ⟨x, (Finset.mem_filter.mp hx₁).2, hx₂, hx⟩

end LeanProofs.GowersSzemeredi
