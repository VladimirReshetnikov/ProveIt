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

private lemma countWhere_cast_eq_sum_ite {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    (countWhere P : Real) = ∑ x : T, if P x then 1 else 0 := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  simp

private lemma fibre_card_cast_eq_sum_ite {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X) (s : ZMod N) :
    ((D.fibre s).card : Real) =
      ∑ x : X, if D.index x = s then 1 else 0 := by
  classical
  unfold MultifunctionDomain.fibre
  rw [Finset.filter_congr_decidable]
  simp

private lemma sum_comp_index_eq_sum_mul_fibre {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (f : ZMod N → Real) :
    (∑ x : X, f (D.index x)) =
      ∑ s : ZMod N, f s * (D.fibre s).card := by
  classical
  simp_rw [fibre_card_cast_eq_sum_ite, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single (D.index x)]
  · simp
  · intro s _ hs
    rw [if_neg (Ne.symm hs)]
    simp
  · simp

/-- The points lying in fibres smaller than the threshold used in Lemma 10.3
occupy at most half of `alpha ^ 2 * M * N` points. -/
private lemma small_anchor_fibre_card_bound {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (alpha : Real) (M : Nat) :
    (countWhere (fun x : X =>
      ¬ alpha ^ 2 * M / 2 ≤ (D.fibreSize x : Real)) : Real) ≤
        alpha ^ 2 * M * N / 2 := by
  classical
  let T : Real := alpha ^ 2 * M / 2
  let f : ZMod N → Real := fun s =>
    if T ≤ (D.fibre s).card then 0 else 1
  have hT : 0 ≤ T := by
    dsimp only [T]
    positivity
  have hcast :
      (countWhere (fun x : X =>
        ¬ alpha ^ 2 * M / 2 ≤ (D.fibreSize x : Real)) : Real) =
        ∑ x : X, f (D.index x) := by
    rw [countWhere_cast_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro x _
    unfold MultifunctionDomain.fibreSize
    by_cases hx : T ≤ ((D.fibre (D.index x)).card : Real)
    · simp [f, T, hx]
    · simp [f, T, hx]
  rw [hcast, sum_comp_index_eq_sum_mul_fibre]
  calc
    (∑ s : ZMod N, f s * (D.fibre s).card) ≤ ∑ _s : ZMod N, T := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : T ≤ ((D.fibre s).card : Real)
      · simp [f, hs, hT]
      · have hle : ((D.fibre s).card : Real) ≤ T := le_of_not_ge hs
        simpa [f, hs] using hle
    _ = T * N := by simp [ZMod.card, mul_comm]
    _ = alpha ^ 2 * M * N / 2 := by
      dsimp only [T]
      ring

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
  classical
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
  have hQnonneg (x : X) : 0 ≤ Q x := by
    dsimp only [Q]
    positivity
  have hEnonneg (x : X) : 0 ≤ E x := by
    exact weightedError_nonneg D phi B x
  have hApos : 0 < A := by
    dsimp only [A]
    have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    have hM' : (0 : Real) < M := by exact_mod_cast hM
    positivity
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
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
          ∑ x : X, if ¬ good x
            then alpha ^ 2 * M ^ 3 * N ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : ¬ good x
        · simp only [if_pos hx]
          exact hQmax x
        · simp [hx]
      _ = (countWhere (fun x : X => ¬ good x) : Real) *
          (alpha ^ 2 * M ^ 3 * N ^ 2) := by
        rw [countWhere_cast_eq_sum_ite, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : ¬ good x <;> simp [hx]
      _ ≤ (alpha ^ 2 * M * N / 2) *
          (alpha ^ 2 * M ^ 3 * N ^ 2) := by
        exact mul_le_mul_of_nonneg_right hsmallCard (by positivity)
      _ = A / 2 := by
        dsimp only [A]
        ring
  have hsplit : QT = QS + ∑ x : X, if ¬ good x then Q x else 0 := by
    dsimp only [QT, QS, S]
    calc
      (∑ x : X, Q x) =
          ∑ x ∈ (Finset.univ : Finset X), Q x := by simp
      _ = (∑ x ∈ (Finset.univ : Finset X) with good x, Q x) +
          ∑ x ∈ (Finset.univ : Finset X) with ¬ good x, Q x :=
        (Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset X) good Q).symm
      _ = (∑ x ∈ Finset.univ.filter good, Q x) +
          ∑ x : X, if ¬ good x then Q x else 0 := by
        simp only [Finset.sum_filter]
  have hQSlower : A / 2 ≤ QS := by
    linarith only [hQTlower, hbadWeight, hsplit]
  have hSne : S.Nonempty := by
    by_contra h
    have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hQSzero : QS = 0 := by simp [QS, hSempty]
    rw [hQSzero] at hQSlower
    linarith only [hApos, hQSlower]
  have hQTle : QT ≤ 2 * QS := by
    linarith only [hsplit, hbadWeight, hQSlower]
  have hEtotal :
      (∑ x : X, E x) ≤ 15 * eta * QT := by
    dsimp only [E, QT, Q]
    simpa only [domainWeightedError, domainTotalWeight, Nat.cast_sum] using
      lemma_10_2_holds N X D phi B alpha M sigma eta hsetup' hsigma
  have hESleTotal : ES ≤ ∑ x : X, E x := by
    dsimp only [ES, S]
    calc
      (∑ x ∈ Finset.univ.filter good, E x) ≤
          ∑ x ∈ (Finset.univ : Finset X), E x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro x _ _
          exact hEnonneg x
      _ = ∑ x : X, E x := by simp
  have hESbound : ES ≤ 30 * eta * QS := by
    calc
      ES ≤ ∑ x : X, E x := hESleTotal
      _ ≤ 15 * eta * QT := hEtotal
      _ ≤ 15 * eta * (2 * QS) := by
        exact mul_le_mul_of_nonneg_left hQTle (mul_nonneg (by norm_num) heta)
      _ = 30 * eta * QS := by ring
  have hScard : (S.card : Real) ≤ Fintype.card X := by
    exact_mod_cast S.card_le_univ
  have hCcard : C * S.card ≤ A := by
    calc
      C * S.card ≤ C * Fintype.card X :=
        mul_le_mul_of_nonneg_left hScard hCnonneg
      _ = A := by
        dsimp only [C, A]
        rw [hcard]
        ring
  by_cases hetaZero : eta = 0
  · have hESzero : ES = 0 := by
      have hESnonneg : 0 ≤ ES := by
        dsimp only [ES]
        apply Finset.sum_nonneg
        intro x _
        exact hEnonneg x
      simpa only [hetaZero, mul_zero, zero_mul] using
        le_antisymm (hESbound.trans (by simp [hetaZero])) hESnonneg
    have hthresholdSum :
        (∑ _x ∈ S, C / 4) ≤ ∑ x ∈ S, Q x := by
      calc
        (∑ _x ∈ S, C / 4) = C * S.card / 4 := by
          simp
          ring
        _ ≤ A / 4 := by linarith only [hCcard]
        _ ≤ A / 2 := by linarith only [hApos]
        _ ≤ QS := hQSlower
        _ = ∑ x ∈ S, Q x := rfl
    obtain ⟨x, hxS, hxQ⟩ :=
      Finset.exists_le_of_sum_le hSne hthresholdSum
    have hxE : E x = 0 := by
      have hxEle : E x ≤ ES := by
        dsimp only [ES]
        exact Finset.single_le_sum (fun y _ => hEnonneg y) hxS
      exact le_antisymm (by linarith only [hxEle, hESzero]) (hEnonneg x)
    refine ⟨x, ?_, ?_, ?_⟩
    · exact (Finset.mem_filter.mp hxS).2
    · exact hxQ
    · dsimp only [E, Q] at hxE ⊢
      simp [hetaZero, hxE]
  · have hetaPos : 0 < eta := lt_of_le_of_ne heta (Ne.symm hetaZero)
    have haverage :
        (∑ _x ∈ S, 15 * eta * C) ≤
          ∑ x ∈ S, (60 * eta * Q x - E x) := by
      calc
        (∑ _x ∈ S, 15 * eta * C) = 15 * eta * (C * S.card) := by
          simp
          ring
        _ ≤ 15 * eta * A := by
          exact mul_le_mul_of_nonneg_left hCcard
            (mul_nonneg (by norm_num) heta)
        _ ≤ 30 * eta * QS := by
          have hscale : 0 ≤ 30 * eta := mul_nonneg (by norm_num) heta
          have h := mul_le_mul_of_nonneg_left hQSlower hscale
          nlinarith only [h]
        _ ≤ 60 * eta * QS - ES := by
          linarith only [hESbound]
        _ = ∑ x ∈ S, (60 * eta * Q x - E x) := by
          dsimp only [QS, ES]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    obtain ⟨x, hxS, hx⟩ := Finset.exists_le_of_sum_le hSne haverage
    have hxE0 : 0 ≤ E x := hEnonneg x
    have hxQ : C / 4 ≤ Q x := by
      have hscale : 0 < 60 * eta := mul_pos (by norm_num) hetaPos
      apply le_of_mul_le_mul_left (a := 60 * eta) (b := C / 4)
        (c := Q x) (by nlinarith only [hx, hxE0]) hscale
    have hxE : E x ≤ 60 * eta * Q x := by
      have hthreshold : 0 ≤ 15 * eta * C := by positivity
      linarith only [hx, hthreshold]
    refine ⟨x, ?_, ?_, ?_⟩
    · exact (Finset.mem_filter.mp hxS).2
    · exact hxQ
    · exact hxE

end LeanProofs.GowersSzemeredi
