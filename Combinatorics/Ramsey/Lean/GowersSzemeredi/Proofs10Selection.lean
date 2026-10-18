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
  rcases hsetup with
    ⟨hbounds, hsigmaPos, heta, hetaOne, hsymmetric, hinvariant, happrox⟩
  rcases hbounds with ⟨halpha, halphaOne, hM, hcard, hfibre⟩
  have hsetup' : Section10Setup D phi B alpha M sigma eta :=
    ⟨⟨halpha, halphaOne, hM, hcard, hfibre⟩, hsigmaPos, heta, hetaOne,
      hsymmetric, hinvariant, happrox⟩
  let good : X → Prop := fun x =>
    alpha ^ 2 * M / 2 ≤ (D.fibreSize x : Real)
  let S : Finset X := Finset.univ.filter good
  let Q : X → Real := fun x => domainTotalWeight D x
  let E : X → Real := fun x => domainWeightedError D phi B x
  let A : Real := alpha ^ 4 * M ^ 4 * N ^ 3
  let C : Real := alpha ^ 3 * M ^ 3 * N ^ 2
  let QT : Real := ∑ x : X, Q x
  let QS : Real := ∑ x ∈ S, Q x
  let ES : Real := ∑ x ∈ S, E x
  have hEnonneg (x : X) : 0 ≤ E x := weightedError_nonneg D phi B x
  have hApos : 0 < A := by
    dsimp only [A]
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    positivity
  have hCnonneg : 0 ≤ C := by positivity
  have hbasic := lemma_10_1_holds N X D alpha M
    ⟨halpha, halphaOne, hM, hcard, hfibre⟩
  have hQmax (x : X) : Q x ≤ alpha ^ 2 * M ^ 3 * N ^ 2 := by
    dsimp only [Q]
    exact_mod_cast hbasic.2.1 x
  have hQTlower : A ≤ QT := by
    dsimp only [A, QT, Q]
    simpa only [domainTotalWeight, Nat.cast_sum] using hbasic.2.2
  have hsmallCard :
      (countWhere (fun x : X => ¬ good x) : Real) ≤
        alpha ^ 2 * M * N / 2 := by
    simpa only [good] using
      small_anchor_fibre_card_bound D alpha M
  have hbadWeight :
      (∑ x : X, if ¬ good x then Q x else 0) ≤ A / 2 := by
    calc
      (∑ x : X, if ¬ good x then Q x else 0) ≤
          ∑ x : X, if ¬ good x then alpha ^ 2 * M ^ 3 * N ^ 2 else 0 :=
        Finset.sum_le_sum fun x _ => by split_ifs; exacts [le_rfl, hQmax x]
      _ = (countWhere (fun x : X => ¬ good x) : Real) *
          (alpha ^ 2 * M ^ 3 * N ^ 2) := by
        rw [countWhere_cast_eq_sum_ite, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
      _ ≤ (alpha ^ 2 * M * N / 2) * (alpha ^ 2 * M ^ 3 * N ^ 2) := by gcongr
      _ = A / 2 := by
        dsimp only [A]
        ring
  have hsplit : QT = QS + ∑ x : X, if ¬ good x then Q x else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_filter_add_sum_filter_not _ good Q).symm
  have hQSlower : A / 2 ≤ QS := by
    linarith only [hQTlower, hbadWeight, hsplit]
  have hSne : S.Nonempty :=
    Finset.nonempty_of_sum_ne_zero (lt_of_lt_of_le (half_pos hApos) hQSlower).ne'
  have hQTle : QT ≤ 2 * QS := by
    linarith only [hsplit, hbadWeight, hQSlower]
  have hEtotal :
      (∑ x : X, E x) ≤ 15 * eta * QT := by
    dsimp only [E, QT, Q]
    simpa only [domainWeightedError, domainTotalWeight, Nat.cast_sum] using
      lemma_10_2_holds N X D phi B alpha M sigma eta hsetup' hsigma
  have hESleTotal : ES ≤ ∑ x : X, E x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun x _ _ => hEnonneg x
  have hESbound : ES ≤ 30 * eta * QS := by
    linarith [mul_le_mul_of_nonneg_left hQTle heta]
  have hCcard : C * S.card ≤ A := by
    calc
      C * S.card ≤ C * Fintype.card X := by
        gcongr
        exact_mod_cast S.card_le_univ
      _ = A := by
        dsimp only [C, A]
        rw [hcard]
        ring
  by_cases hetaZero : eta = 0
  · have hESzero : ES = 0 :=
      le_antisymm (by simpa [hetaZero] using hESbound) (Finset.sum_nonneg fun x _ => hEnonneg x)
    have hthresholdSum :
        (∑ _x ∈ S, C / 4) ≤ ∑ x ∈ S, Q x := by
      show _ ≤ QS
      rw [Finset.sum_const, nsmul_eq_mul]
      linarith only [hCcard, hApos, hQSlower]
    obtain ⟨x, hxS, hxQ⟩ :=
      Finset.exists_le_of_sum_le hSne hthresholdSum
    have hxE : E x = 0 := le_antisymm (by
      linarith only [show E x ≤ ES from Finset.single_le_sum (fun y _ => hEnonneg y) hxS,
        hESzero]) (hEnonneg x)
    refine ⟨x, (Finset.mem_filter.mp hxS).2, hxQ, ?_⟩
    dsimp only [E, Q] at hxE ⊢
    simp [hetaZero, hxE]
  · have hetaPos : 0 < eta := lt_of_le_of_ne heta (Ne.symm hetaZero)
    have haverage :
        (∑ _x ∈ S, 15 * eta * C) ≤
          ∑ x ∈ S, (60 * eta * Q x - E x) := by
      have hsum : ∑ x ∈ S, (60 * eta * Q x - E x) = 60 * eta * QS - ES := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hsum, Finset.sum_const, nsmul_eq_mul]
      linarith [mul_le_mul_of_nonneg_left hCcard heta, mul_le_mul_of_nonneg_left hQSlower heta]
    obtain ⟨x, hxS, hx⟩ := Finset.exists_le_of_sum_le hSne haverage
    have hxE0 : 0 ≤ E x := hEnonneg x
    have hxQ : C / 4 ≤ Q x := by
      have hscale : 0 < 60 * eta := mul_pos (by norm_num) hetaPos
      apply le_of_mul_le_mul_left (a := 60 * eta) (b := C / 4)
        (c := Q x) (by nlinarith only [hx, hxE0]) hscale
    have hxE : E x ≤ 60 * eta * Q x := by
      have hthreshold : 0 ≤ 15 * eta * C := by positivity
      linarith only [hx, hthreshold]
    exact ⟨x, (Finset.mem_filter.mp hxS).2, hxQ, hxE⟩

end LeanProofs.GowersSzemeredi
