import GowersSzemeredi.Proofs10Bohr

/-!
# The induced-difference assertion in Lemma 10.12

This file proves the final intersection argument that identifies differences
of `phi` on the regular set with the homomorphism induced on the smaller Bohr
neighborhood.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

@[simp] private lemma mem_inducedTranslate_iff {N : Nat}
    (A : Finset (ZMod N)) (d x : ZMod N) :
    x ∈ section10Translate A d ↔ x - d ∈ A := by norm_num

theorem lemma_10_12_holds : lemma_10_12 := by
  classical
  intro N _ X _ _ D phi K delta theta W B' psi psi1 hK hdelta hdeltaOne hsqrt hfibre
  dsimp only
  intro hlocal _ hinduced w1 hw1 w2 hw2 hc
  set B := bohr K delta
  set c := D.index w1 - D.index w2 with hcdef
  let Good (w : X) (d : ZMod N) : Prop :=
    AlmostEvery (1 - theta) (D.fibre (D.index w + d)) fun z => phi z - phi w = psi d
  let G1 := B'.filter (Good w1)
  let G2 := B'.filter (Good w2)
  rw [section10RegularSet, Finset.mem_filter] at hw1 hw2
  have hG1 : (1 - Real.sqrt theta) * (B'.card : Real) ≤ G1.card := hw1.2
  have hG2 : (1 - Real.sqrt theta) * (B'.card : Real) ≤ G2.card := hw2.2
  have hθ : theta < 25 / 256 := by linarith [Real.lt_sq_of_sqrt_lt hsqrt]
  have hB : (0 : Real) < B.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, bohr_zero_mem K delta hdelta.le⟩
  -- `G2` and `G1 + c` are large subsets of `B ∪ (B + c)`, which has at most `9/8 |B|` points
  have hoverlap : (7 / 8 : Real) * B.card ≤ (B ∩ section10Translate B c).card :=
    corollary_10_11_overlap K delta hK hdelta hdeltaOne c hc
  have hunion : ((B ∪ section10Translate B c).card : Real) +
      (B ∩ section10Translate B c).card = B.card + B.card := by
    norm_cast
    rw [Finset.card_union_add_card_inter, section10Translate_card]
  have hinter := inter_card_lower_of_subsets G2 (section10Translate G1 c)
    (B ∪ section10Translate B c)
    ((Finset.filter_subset _ _).trans (hlocal.1.trans Finset.subset_union_left))
    ((section10Translate_mono ((Finset.filter_subset _ _).trans hlocal.1) c).trans
      Finset.subset_union_right)
  rw [section10Translate_card] at hinter
  obtain ⟨x, hx⟩ : (G2 ∩ section10Translate G1 c).Nonempty := by
    rw [← Finset.card_pos, ← Nat.cast_pos (α := Real)]
    linarith [hlocal.2.1, mul_le_mul_of_nonneg_right hθ.le hB.le,
      mul_le_mul_of_nonneg_right hsqrt.le (Nat.cast_nonneg B'.card : (0 : Real) ≤ B'.card)]
  simp only [Finset.mem_inter, Finset.mem_filter, mem_inducedTranslate_iff, G1, G2] at hx
  obtain ⟨⟨hxB', hGood2⟩, hxcB', hGood1⟩ := hx
  have hindex : D.index w1 + (x - c) = D.index w2 + x := by rw [hcdef]; abel
  -- both conditions hold on more than half of the fibre over `index w2 + x`
  obtain ⟨z, hz⟩ : ((D.fibre (D.index w2 + x)).filter fun z =>
      phi z - phi w1 = psi (x - c) ∧ phi z - phi w2 = psi x).Nonempty := by
    simp only [Good, hindex, AlmostEvery] at hGood1 hGood2
    rw [Finset.filter_congr_decidable] at hGood1 hGood2
    have hF : (0 : Real) < (D.fibre (D.index w2 + x)).card := by
      exact_mod_cast (hfibre w2 hw2.1 x hxB').card_pos
    rw [← Finset.card_pos, Finset.filter_and, ← Nat.cast_pos (α := Real)]
    refine lt_of_lt_of_le ?_ (inter_card_lower_of_subsets _ _ _ (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))
    linarith [mul_lt_mul_of_pos_right hθ hF]
  obtain ⟨-, heq1, heq2⟩ := Finset.mem_filter.mp hz
  calc phi w1 - phi w2 = (phi z - phi w2) - (phi z - phi w1) := by abel
    _ = psi x - psi (x - c) := by rw [heq2, heq1]
    _ = psi1 c := hinduced c hc x hxB' (x - c) hxcB' (by abel)

end LeanProofs.GowersSzemeredi
