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
  rcases hG with ⟨hstep, hproper, hsub, hlower, hB, hrel, habs, hlinear⟩
  have hcard : G.S.carrier.card = G.S.length := hproper
  let I := criticalHeights S D E
  let δ : Real := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224
  let β : Real := (2 : Real) ^ (-(48 : Int)) * S.alpha ^ 256
  let K : Real := (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704
  have hα : 0 < S.alpha := S.alpha_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hcancel : K * ((2 : Real) ^ 135 * S.alpha ^ (-(704 : Int))) = 1 := by
    dsimp [K]
    norm_num [zpow_neg, zpow_natCast]
    field_simp
  have hwidth : 1 ≤ K * G.S.length := by
    calc
      1 = K * ((2 : Real) ^ 135 * S.alpha ^ (-(704 : Int))) := hcancel.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsize hK.le
  have hn : 0 < G.S.length := by
    by_contra hn
    have hz : G.S.length = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hwidth
    norm_num at hwidth
  have hS : G.S.carrier.Nonempty := by
    apply Finset.card_pos.mp
    simpa only [hcard] using hn
  have hD : δ ^ 2 * β = 2 * K := by
    dsimp [δ, β, K]
    norm_num [zpow_neg, zpow_natCast]
    ring
  have hrow := exists_translated_row_coefficients G.S.carrier I G.B G.y S.phi
    (fun z hz ↦ (Finset.mem_product.mp (hB hz)).1) hlinear
  by_cases hm : E.Q.length = 0
  · obtain ⟨a, c, hrow⟩ := hrow
    refine ⟨⟨a, c, ∅, ∅⟩, hrow, Finset.empty_subset _, ?_, ?_, ?_⟩
    · simpa only [FreimanHom, Finset.coe_empty] using
        (isAddFreimanHom_empty (n := 8) (B := Set.univ) (f := fun h ↦ (a h, c h)))
    · simp
    · simp [hm]
  have hmpos : (0 : Real) < E.Q.length := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hIm : (I.card : Real) ≤ E.Q.length := by
    have hi : I ⊆ E.Q.carrier := fun h hh ↦
      (Finset.mem_inter.mp (Finset.mem_filter.mp hh).1).1
    have hq : E.Q.carrier.card ≤ E.Q.length := by
      unfold ModAP.carrier
      simpa only [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_image_le (s := (Finset.univ : Finset (Fin E.Q.length)))
          (f := fun i : Fin E.Q.length ↦ E.Q.start + (i : Nat) * E.Q.step))
    exact_mod_cast (Finset.card_le_card hi).trans hq
  obtain ⟨a, c, J, hrow, hJI, hfreiman, hmass⟩ :=
    exists_freiman_common_rows_of_two_densities S G.S.carrier I G.B G.y hS hBA hB
      hlinear hδ hβ hmpos hIm
      (by simpa only [hcard] using hrel)
      (by simpa only [hcard] using habs)
      (by rw [hD, hcard]; nlinarith)
  refine ⟨⟨a, c, J, G.B.filter fun z ↦ z.2 - G.y ∈ J⟩,
    hrow, hJI, hfreiman, rfl, ?_⟩
  change K * E.Q.length * G.S.length ≤ _
  rw [hD, hcard] at hmass
  have hround : K * E.Q.length * G.S.length ≤
      E.Q.length * (2 * K * G.S.length - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hwidth hmpos.le]
  exact hround.trans hmass

/-- The repaired catalogue statement, with all quantitative selection and
coefficient-extraction obligations discharged. -/
theorem lemma_13_8_holds : lemma_13_8 := by
  intro N _ S D E F G hG hsize
  exact lemma_13_8_with_domain S D E F G hG.1 hG.2 hsize

end LeanProofs.GowersSzemeredi
