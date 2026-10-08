import GowersSzemeredi.Proofs16CubicCoverControls
import GowersSzemeredi.Proofs16PowerCoverTransport

/-! Transfer sufficiently-wide-box covers to all proper boxes.
Cap the positive exponent so that every box below the starting threshold
has target width at most two. The exact coarse relation cover then handles
the short boxes with no exceptional points. All constants remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def section16CappedWidthExponent (e T : Real) : Real :=
  min e (Real.log 2 / Real.log (max 2 T))

theorem section16CappedWidthExponent_pos {e T : Real} (he : 0 < e) :
    0 < section16CappedWidthExponent e T := by
  have hT : 1 < max (2 : Real) T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  exact lt_min he (div_pos (Real.log_pos (by norm_num)) (Real.log_pos hT))

theorem section16CappedWidthExponent_small {e T : Real} (he : 0 < e)
    {W : Nat} (hW : (W : Real) ≤ T) :
    (W : Real) ^ section16CappedWidthExponent e T ≤ 2 := by
  have hM : (1 : Real) < max 2 T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hMpos : (0 : Real) < max 2 T := zero_lt_one.trans hM
  have hlog := Real.log_pos hM
  have hcancel : Real.log (max 2 T) * (Real.log 2 / Real.log (max 2 T)) = Real.log 2 := by
    field_simp
  calc
    (W : Real) ^ section16CappedWidthExponent e T
        ≤ (max 2 T) ^ section16CappedWidthExponent e T :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (hW.trans (le_max_right _ _))
        (section16CappedWidthExponent_pos he).le
    _ ≤ (max 2 T) ^ (Real.log 2 / Real.log (max 2 T)) :=
      Real.rpow_le_rpow_of_exponent_le hM.le (min_le_right _ _)
    _ = 2 := by
      rw [Real.rpow_def_of_pos hMpos, hcancel, Real.exp_log (by norm_num : (0 : Real) < 2)]

/-- Explicit large-box profiles and bounded fibres give multiple
multilinearity with capped exponents on every proper box. -/
theorem multiplyLinearWith_of_large_box_covers {N k : Nat} [NeZero N]
    (hk : 0 < k) {Gamma : Finset (Point N k × ZMod N)}
    (M : Nat) (hfib : ∀ x : Point N k, (Gamma.filter fun z => z.1 = x).card ≤ M)
    (Q E T : Real → Real)
    (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s)
    (hcover : ∀ s, 0 < s → s ≤ 1 → LargeBoxMultilinearCover Gamma s (Q s) (E s) (T s)) :
    MultiplyLinearWith
      (fun s => max (Q s) ((3 ^ k * M : Nat) : Real))
      (fun s => section16CappedWidthExponent (E s) (T s)) Gamma := by
  intro s hs hs1 P hP
  have he := hE s hs hs1
  have hc := section16CappedWidthExponent_pos (T := T s) he
  by_cases hlarge : T s ≤ (P.width : Real)
  · obtain ⟨L, q, H, R, mu, hH, hmass, hpart, hproper, hq, hw, hmu, hcov⟩ :=
      hcover s hs hs1 P hP hlarge
    refine ⟨L, q, H, R, mu, hH, hmass, hpart, hproper,
      hq.trans (le_max_left _ _), ?_, hmu, hcov⟩
    intro j
    by_cases hz : P.width = 0
    · simp only [hz, Nat.cast_zero, Real.zero_rpow hc.ne']
      exact Nat.cast_nonneg _
    · have hW : (1 : Real) ≤ P.width := by exact_mod_cast (show 1 ≤ P.width by omega)
      exact (Real.rpow_le_rpow_of_exponent_le hW (min_le_left _ _)).trans (hw j)
  · have hsmall := section16CappedWidthExponent_small (W := P.width) he (lt_of_not_ge hlarge).le
    obtain ⟨L, R, mu, hpart, hproper, hw, hmu, hcov⟩ :=
      section16_coarse_relation_cover hk Gamma M hfib P hP
    refine ⟨L, 3 ^ k * M, P.carrier, R, mu, Finset.Subset.refl _, ?_,
      hpart, hproper, le_max_right _ _, ?_, hmu, fun j x hx _ y hy => hcov j x hx y hy⟩
    · nlinarith [mul_nonneg hs.le (Nat.cast_nonneg P.carrier.card : (0 : Real) ≤ P.carrier.card)]
    · intro j
      have hmin : (P.width : Real) ^ section16CappedWidthExponent (E s) (T s) ≤
          ((min 2 P.width : Nat) : Real) := by
        rcases Nat.lt_or_ge P.width 2 with hlt | hge
        · rw [min_eq_right hlt.le]
          interval_cases h : P.width
          · simp [Real.zero_rpow hc.ne']
          · simp
        · rw [min_eq_left hge]
          exact_mod_cast hsmall
      exact hmin.trans (by exact_mod_cast hw j)

end LeanProofs.GowersSzemeredi
