import GowersSzemeredi.Proofs13AllScaleStage139
import GowersSzemeredi.Proofs13BilinearRestriction

/-! Square extraction from the geometry retained by the actual constructions,
including the tiny height cells used for short columns. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A height cell of at most three points requires only a singleton square.
The retained mass supplies a point in the original bilinear piece. -/
theorem corollary_13_10_of_tiny_cell {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) (J : Stage139Data N)
    (h139 : IsStage139Data S E G H J) (hGpos : 0 < G.S.length)
    (hUpos : 0 < J.U.length) (hsmall : J.U.length ≤ 3) :
    ∃ V W : ModAP N, ∃ E' : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧
      V.length = W.length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ V.length ∧
      E' ⊆ J.D ∧ E' ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤ E'.card ∧
      BilinearOn E' S.phi := by
  classical
  have hmass : (0 : Real) < J.D.card := lt_of_lt_of_le (by
    have hG : (0 : Real) < G.S.length := by exact_mod_cast hGpos
    have hU : (0 : Real) < J.U.length := by exact_mod_cast hUpos
    have hα := S.alpha_pos
    positivity) h139.2.2.2.2.2.2.1
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by exact_mod_cast hmass)
  let V : ModAP N := ⟨z.1, J.U.step, 1⟩
  let W : ModAP N := ⟨z.2, J.U.step, 1⟩
  have hV : V.carrier = {z.1} := by simp [V, ModAP.carrier]
  have hW : W.carrier = {z.2} := by simp [W, ModAP.carrier]
  have hsub : ({z} : Finset (Pair N)) ⊆ J.D := by simpa
  refine ⟨V, W, {z}, h139.1, rfl, ?_, ?_, rfl, ?_, hsub, ?_, ?_, ?_⟩
  · change V.carrier.card = 1
    simp [hV]
  · change W.carrier.card = 1
    simp [hW]
  · simp only [V, Nat.cast_one]
    rw [← Real.sqrt_eq_rpow]
    have h := Real.sqrt_le_sqrt (show (J.U.length : Real) ≤ 4 by exact_mod_cast (show J.U.length ≤ 4 by omega))
    rw [show Real.sqrt 4 = 2 by exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)] at h
    linarith only [h]
  · simp [hV, hW]
  · change (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * (1 : Nat) * (1 : Nat) ≤ ({z} : Finset (Pair N)).card
    simp only [Nat.cast_one, mul_one, Finset.card_singleton]
    calc
      _ ≤ (2 : Real) ^ (-(137 : Int)) * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ S.alpha_pos.le S.alpha_at_most_one) (by positivity)
      _ ≤ 1 := by norm_num
  · obtain ⟨mu, hmu, hagree⟩ := h139.2.2.2.2.2.2.2
    exact ⟨mu, hmu, fun w hw ↦ hagree w (hsub hw)⟩

/-- The two alternatives produced by Stage 13.9 suffice for the full square
bound, with no scale threshold and no assumed grid partition. -/
theorem corollary_13_10_of_construction_geometry {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) (J : Stage139Data N)
    (h139 : IsStage139Data S E G H J) (hS : G.S.IsProper) (hGpos : 0 < G.S.length)
    (hsupport : J.D ⊆ G.S.carrier.product (translateFinset J.U.carrier G.y))
    (hgeom : J.U.length ≤ 3 ∨ ∃ t : Nat, 0 < t ∧
      J.U.step = (t : ZMod N) * G.S.step ∧ t * (J.U.length - 1) < G.S.length) :
    ∃ V W : ModAP N, ∃ E' : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧
      V.length = W.length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ V.length ∧
      E' ⊆ J.D ∧ E' ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤ E'.card ∧
      BilinearOn E' S.phi := by
  have hUpos : 0 < J.U.length := by
    have hpos : (0 : Real) < J.U.length :=
      (Real.rpow_pos_of_pos (by exact_mod_cast hGpos) _).trans_le h139.2.2.2.2.1
    exact_mod_cast hpos
  by_cases hsmall : J.U.length ≤ 3
  · exact corollary_13_10_of_tiny_cell S E G H J h139 hGpos hUpos hsmall
  obtain ⟨t, ht, hstep, hspan⟩ := hgeom.resolve_left hsmall
  have hsqrt : Nat.sqrt J.U.length ≤ J.U.length - 1 := by
    have := Nat.sqrt_lt_self (by omega : 1 < J.U.length)
    omega
  exact corollary_13_10_of_integer_step_fit S E G H J h139 hS hsupport hUpos t ht hstep
    ((Nat.mul_le_mul_left t hsqrt).trans hspan.le)

end LeanProofs.GowersSzemeredi
