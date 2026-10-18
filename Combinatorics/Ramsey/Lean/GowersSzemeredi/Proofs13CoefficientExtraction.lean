import GowersSzemeredi.Proofs13CommonRows

/-!
# The quantitative coefficient extraction of Lemma 13.8

The proof uses the corrected upstream densities `2^-43 * alpha^224` and
`2^-48 * alpha^256`. It explicitly restores primality and containment of B
in the original domain, which are required by the printed argument.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

/-- Lemma 13.8 with its standing field and original-domain hypotheses. -/
theorem lemma_13_8_with_domain {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (F : Stage136Data N) (G : Stage137Data N)
    (hG : IsStage137DataWithoutDomain S D E F G) (hBA : G.B ⊆ S.A)
    (hsize : (2 : Real) ^ 135 * S.alpha ^ (-(704 : Int)) ≤ G.S.length) :
    ∃ H : Stage138Data N, IsStage138Data S D E G H := by
  classical
  rcases hG with ⟨_, hproper, _, _, hB, hrel, habs, hlinear⟩
  have hcard : G.S.carrier.card = G.S.length := hproper
  let δ : Real := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224
  let β : Real := (2 : Real) ^ (-(48 : Int)) * S.alpha ^ 256
  let K : Real := (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704
  have hα := S.alpha_pos
  have hwidth : 1 ≤ K * G.S.length := by
    rw [zpow_neg, zpow_ofNat, mul_inv_le_iff₀ (by positivity)] at hsize
    simp only [K, zpow_neg, zpow_ofNat]
    linarith
  have hS : G.S.carrier.Nonempty := by
    rw [← Finset.card_pos, hcard, Nat.pos_iff_ne_zero]
    rintro h
    norm_num [h] at hwidth
  have hD : δ ^ 2 * β = 2 * K := by
    simp only [δ, β, K, zpow_neg, zpow_ofNat]
    ring
  have hrow := exists_translated_row_coefficients G.S.carrier (criticalHeights S D E) G.B G.y
    S.phi (fun z hz ↦ (Finset.mem_product.mp (hB hz)).1) hlinear
  by_cases hm : E.Q.length = 0
  · obtain ⟨a, c, hrow⟩ := hrow
    refine ⟨⟨a, c, ∅, ∅⟩, hrow, Finset.empty_subset _, ?_, by simp, by simp [hm]⟩
    simpa only [FreimanHom, Finset.coe_empty] using
      (isAddFreimanHom_empty (n := 8) (B := Set.univ) (f := fun h ↦ (a h, c h)))
  have hmpos : (0 : Real) < E.Q.length := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hIm : ((criticalHeights S D E).card : Real) ≤ E.Q.length := by
    exact_mod_cast (Finset.card_le_card ((Finset.filter_subset _ _).trans
      Finset.inter_subset_left)).trans (Finset.card_image_le.trans (Finset.card_fin _).le)
  obtain ⟨a, c, J, hrow, hJI, hfreiman, hmass⟩ :=
    exists_freiman_common_rows_of_two_densities (δ := δ) (β := β) S G.S.carrier _ G.B G.y hS
      hBA hB hlinear (by positivity) (by positivity) hmpos hIm (by simpa only [hcard] using hrel)
      (by simpa only [hcard] using habs) (by rw [hD, hcard]; linarith)
  refine ⟨⟨a, c, J, _⟩, hrow, hJI, hfreiman, rfl, le_trans ?_ hmass⟩
  rw [hD, hcard]
  linarith [mul_le_mul_of_nonneg_left hwidth hmpos.le]

/-- The repaired catalogue statement, with all quantitative selection and
coefficient-extraction obligations discharged. -/
theorem lemma_13_8_holds : lemma_13_8 := by
  intro N _ S D E F G hG hsize
  exact lemma_13_8_with_domain S D E F G hG.1 hG.2 hsize

end LeanProofs.GowersSzemeredi
