import GowersSzemeredi.Proofs13SingletonEdgeCells
import GowersSzemeredi.Proofs13CommonStepSelection

/-! The small target-length case of Lemma 13.6 needs only a single column,
whose linearity follows directly from the vertical Freiman hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section13_column_mass_selection {N : Nat} [NeZero N]
    (S : Section13Context N) (I : Finset (ZMod N)) (delta : Real)
    (hY : ∀ h ∈ I, delta * (N : Real) ^ 2 ≤ (verticalEdgeDomain S.A h).card) :
    ∃ x : ZMod N, delta * N * I.card ≤ ∑ h ∈ I, (verticalEdgeFiberCount S.A h x : Real) := by
  classical
  have hf (h : ZMod N) : (∑ x : ZMod N, verticalEdgeFiberCount S.A h x) =
      (verticalEdgeDomain S.A h).card := by
    exact (Finset.card_eq_sum_card_fiberwise (s := verticalEdgeDomain S.A h)
      (t := Finset.univ) (f := Prod.fst) (by simp)).symm
  have hsum : (∑ _x : ZMod N, delta * N * I.card) ≤
      ∑ x : ZMod N, ∑ h ∈ I, (verticalEdgeFiberCount S.A h x : Real) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ _h ∈ I, delta * (N : Real) ^ 2 := by simp; ring
      _ ≤ ∑ h ∈ I, ((verticalEdgeDomain S.A h).card : Real) := Finset.sum_le_sum hY
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h _
        exact_mod_cast (hf h).symm
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨x, hx⟩

theorem lemma_13_6_small_row_scale {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (E : Stage135Data N)
    (h135 : IsStage135Data S D E)
    (hscale : section13Zeta S.alpha / 2 *
      (N : Real) ^ ((1 : Real) / (2 : Real) ^ (13 * section13Q S.alpha)) ≤ 1) :
    ∃ F : Stage136Data N, IsStage136Data S D E F := by
  classical
  let delta : Real := (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 224
  have hdelta : delta ≤ S.alpha ^ 32 / 16 := by
    have hp : S.alpha ^ 224 ≤ S.alpha ^ 32 := by
      calc
        _ = S.alpha ^ 32 * S.alpha ^ 192 := by rw [← pow_add]
        _ ≤ S.alpha ^ 32 * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one) (by positivity)
        _ = _ := mul_one _
    calc
      _ ≤ (2 : Real) ^ (-(43 : Int)) * S.alpha ^ 32 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ (1 / 16 : Real) * S.alpha ^ 32 :=
        mul_le_mul_of_nonneg_right (by norm_num [zpow_neg]) (by positivity)
      _ = _ := by ring
  have hY (h : ZMod N) (hh : h ∈ criticalHeights S D E) :
      delta * (N : Real) ^ 2 ≤ (verticalEdgeDomain S.A h).card :=
    (mul_le_mul_of_nonneg_right hdelta (by positivity)).trans
      (section13_strong_height_edge_density S h (Finset.mem_filter.mp hh).2)
  obtain ⟨x, hx⟩ := section13_column_mass_selection S (criticalHeights S D E) delta hY
  let R : ModAP N := ⟨x, E.Q.step, 1⟩
  let F : Stage136Data N := ⟨R, verticalEdgeDomain S.A⟩
  have hR : R.carrier = {x} := by simp [R, ModAP.carrier]
  have hF (h : ZMod N) : stage136RestrictedEdges F h =
      (verticalEdgeDomain S.A h).filter (fun z => z.1 = x) := by
    simp only [stage136RestrictedEdges, F, hR, Finset.mem_singleton]
  have hmass : delta * F.R.length * N * (criticalHeights S D E).card ≤
      ∑ h ∈ criticalHeights S D E, ((stage136RestrictedEdges F h).card : Real) := by
    simpa only [F, R, Nat.cast_one, mul_one, hF, verticalEdgeFiberCount] using hx
  refine ⟨F, rfl, h135.1, ?_, ?_, ?_, ?_, ?_⟩
  · change R.carrier.card = 1
    rw [hR, Finset.card_singleton]
  · simpa only [F, R, Nat.cast_one] using hscale
  · intro h hh
    refine ⟨Finset.Subset.refl _, hY h hh, ?_⟩
    rw [hF]
    exact section13_single_column_linear S h x
  · simpa only [Nat.cast_sum] using hmass
  · simp only [Nat.cast_sum]
    have hI : S.alpha ^ 32 * E.Q.length / 32 ≤ (criticalHeights S D E).card := by
      have hc := h135.2.2.2.2.2
      have hn : 0 ≤ S.alpha ^ 32 * (E.Q.length : Real) := by positivity
      linarith only [hc, hn]
    calc
      _ = delta * F.R.length * N * (S.alpha ^ 32 * E.Q.length / 32) := by
        dsimp only [delta]
        rw [show (256 : Nat) = 224 + 32 by omega, pow_add]
        norm_num [zpow_neg]
        ring
      _ ≤ delta * F.R.length * N * (criticalHeights S D E).card :=
        mul_le_mul_of_nonneg_left hI (by dsimp [delta]; positivity)
      _ ≤ _ := hmass

end LeanProofs.GowersSzemeredi
