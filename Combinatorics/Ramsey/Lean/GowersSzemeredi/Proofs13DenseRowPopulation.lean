import GowersSzemeredi.Proofs13DenseRows

/-! Quantitative selection of rows with density greater than four fifths. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

noncomputable def section13DenseRows {N : Nat} [NeZero N]
    (A : Finset (Pair N)) : Finset (ZMod N) := by
  classical
  exact Finset.univ.filter fun y ↦ 4 * N < 5 * (horizontalSection A y).card

noncomputable def section13DenseRowPiece {N : Nat} [NeZero N]
    (A : Finset (Pair N)) : Finset (Pair N) := by
  classical
  exact A.filter fun z ↦ z.2 ∈ section13DenseRows A

theorem section13_bad_rows_bound {N : Nat} [NeZero N]
    (S : Section13Context N) :
    ((Finset.univ \ section13DenseRows S.A).card : Real) ≤
      5 * (1 - S.alpha) * N := by
  classical
  let Bad := Finset.univ \ section13DenseRows S.A
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hnonneg (y : ZMod N) : 0 ≤ (N : Real) - (horizontalSection S.A y).card := by
    apply sub_nonneg.mpr
    exact_mod_cast (show (horizontalSection S.A y).card ≤ N by
      simpa only [ZMod.card] using Finset.card_le_univ (horizontalSection S.A y))
  have hbad (y : ZMod N) (hy : y ∈ Bad) :
      (N : Real) / 5 ≤ (N : Real) - (horizontalSection S.A y).card := by
    have hnot : ¬ 4 * N < 5 * (horizontalSection S.A y).card := by
      intro hd
      exact (Finset.mem_sdiff.mp hy).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
    have hle : 5 * (horizontalSection S.A y).card ≤ 4 * N := Nat.not_lt.mp hnot
    have hleR : 5 * ((horizontalSection S.A y).card : Real) ≤ 4 * N := by exact_mod_cast hle
    linarith
  have hsum : (∑ y : ZMod N, ((N : Real) - (horizontalSection S.A y).card)) =
      (1 - S.alpha) * (N : Real) ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, ← Nat.cast_sum, sum_horizontalSection_card, S.card_A]
    ring
  have hmass : (Bad.card : Real) * N / 5 ≤
      ∑ y ∈ Bad, ((N : Real) - (horizontalSection S.A y).card) := by
    calc
      _ = ∑ _y ∈ Bad, (N : Real) / 5 := by simp; ring
      _ ≤ _ := Finset.sum_le_sum hbad
  have hsubsum : (∑ y ∈ Bad, ((N : Real) - (horizontalSection S.A y).card)) ≤
      ∑ y : ZMod N, ((N : Real) - (horizontalSection S.A y).card) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ ↦ hnonneg y)
  have htotal := hmass.trans (hsubsum.trans hsum.le)
  apply le_of_mul_le_mul_right (a := (N : Real)) _ hN
  change (Bad.card : Real) * N ≤ (5 * (1 - S.alpha) * N) * N
  nlinarith only [htotal]

theorem section13_dense_rows_large {N : Nat} [NeZero N]
    (S : Section13Context N) (hα : 14 / 15 < S.alpha) :
    2 * N < 3 * (section13DenseRows S.A).card := by
  classical
  have hbad := section13_bad_rows_bound S
  have hparts : (Finset.univ \ section13DenseRows S.A).card +
      (section13DenseRows S.A).card = N := by
    simpa only [Finset.univ_inter, Finset.card_univ, ZMod.card] using
      Finset.card_sdiff_add_card_inter (Finset.univ : Finset (ZMod N)) (section13DenseRows S.A)
  have hpartsR : ((Finset.univ \ section13DenseRows S.A).card : Real) +
      (section13DenseRows S.A).card = N := by exact_mod_cast hparts
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hc : 5 * (1 - S.alpha) < (1 / 3 : Real) := by linarith
  have hb : ((Finset.univ \ section13DenseRows S.A).card : Real) < (1 / 3 : Real) * N :=
    hbad.trans_lt (mul_lt_mul_of_pos_right hc hN)
  exact_mod_cast (show (2 : Real) * N < 3 * (section13DenseRows S.A).card by
    linarith only [hb, hpartsR])

theorem section13_dense_row_piece_mass {N : Nat} [NeZero N]
    (S : Section13Context N) :
    (6 * S.alpha - 5) * (N : Real) ^ 2 ≤ (section13DenseRowPiece S.A).card := by
  classical
  let Bad := Finset.univ \ section13DenseRows S.A
  let C := S.A.filter fun z ↦ z.2 ∉ section13DenseRows S.A
  have hCsub : C ⊆ Finset.univ.product Bad := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩⟩
  have hCcard : C.card ≤ N * Bad.card := by
    have hc := Finset.card_le_card hCsub
    rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, ZMod.card] at hc
    exact hc
  have hCcardR : (C.card : Real) ≤ (N : Real) * Bad.card := by exact_mod_cast hCcard
  have hparts : (section13DenseRowPiece S.A).card + C.card = S.A.card := by
    exact Finset.card_filter_add_card_filter_not (s := S.A)
      (fun z ↦ z.2 ∈ section13DenseRows S.A)
  have htotalR : ((section13DenseRowPiece S.A).card : Real) + C.card =
      S.alpha * (N : Real) ^ 2 := by
    rw [← S.card_A]
    exact_mod_cast hparts
  have hbad : (Bad.card : Real) ≤ 5 * (1 - S.alpha) * N := section13_bad_rows_bound S
  have hN : (0 : Real) ≤ N := Nat.cast_nonneg _
  have hCupper := hCcardR.trans (mul_le_mul_of_nonneg_left hbad hN)
  nlinarith only [hCupper, htotalR]

theorem section13_dense_rows_affine {N : Nat} [NeZero N]
    (S : Section13Context N) :
    ∀ y ∈ section13DenseRows S.A, ∃ a c : ZMod N,
      ∀ x ∈ horizontalSection S.A y, S.phi (x, y) = a + c * x := by
  intro y hy
  have hgood : 4 * N < 5 * (horizontalSection S.A y).card := (Finset.mem_filter.mp hy).2
  have hdense : 2 * N < 3 * (horizontalSection S.A y).card := by omega
  obtain ⟨c, a, hrow⟩ := dense_freiman_eight_linear (horizontalSection S.A y)
    (fun x ↦ S.phi (x, y)) (S.separately_freiman.2 y) hdense
  exact ⟨a, c, fun x hx ↦ (hrow x hx).trans (add_comm _ _)⟩

end LeanProofs.GowersSzemeredi
