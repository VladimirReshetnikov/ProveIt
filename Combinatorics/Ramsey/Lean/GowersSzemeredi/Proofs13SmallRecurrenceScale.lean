import GowersSzemeredi.Proofs13QuadraticRecurrence

/-! The singleton branch of Lemma 13.5 when the affine tolerance is at
least half the modulus. This uses no primality or large-modulus assumption.

`lemma_13_5_small_recurrence_scale` and `lemma_13_5_small_scale` are in
`Proofs13SmallRecurrenceScaleSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem centeredAbs_le_half_modulus {N : Nat} [NeZero N] (x : ZMod N) :
    (centeredAbs x : Real) ≤ (N : Real) / 2 := by
  have h : centeredAbs x * 2 ≤ N := (Nat.mul_le_mul_right 2 (ZMod.natAbs_valMinAbs_le x)).trans
    (Nat.div_mul_le_self N 2)
  have hR : (centeredAbs x : Real) * 2 ≤ N := by exact_mod_cast h
  linarith only [hR]

theorem lemma_13_5_empty_progression {N : Nat} [NeZero N]
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) (hL : D.P.length = 0) :
    ∃ E : Stage135Data N, IsStage135Data S D E := by
  have hPempty : D.P.carrier = ∅ := Finset.card_eq_zero.mp (h134.2.2.1.trans hL)
  refine ⟨⟨D.P⟩, h134.2.1, h134.2.2.1, Finset.Subset.rfl, ?_, ?_, ?_⟩
  · change (D.P.length : Real) ^ ((1 : Real) / (2 : Real) ^ (12 * D.q)) / 2 ≤ D.P.length
    simp only [hL, Nat.cast_zero, Real.zero_rpow (by positivity : (1 : Real) / 2 ^ (12 * D.q) ≠ 0), zero_div, le_refl]
  · intro i h hh
    rw [hPempty] at hh
    exact (Finset.notMem_empty h hh).elim
  · change S.alpha ^ 32 * (D.P.length : Real) / 20 ≤ _
    rw [hL, Nat.cast_zero, mul_zero, zero_div]
    exact Nat.cast_nonneg _

end LeanProofs.GowersSzemeredi
