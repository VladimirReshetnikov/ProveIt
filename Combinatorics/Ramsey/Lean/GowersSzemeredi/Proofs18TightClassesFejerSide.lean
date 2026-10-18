import GowersSzemeredi.Proofs18TightClassesFejer
import GowersSzemeredi.Proofs16SplitStepFejerSide

/-! Declarations of `Proofs18TightClassesFejer` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- **The class cover in dimension `l` at degree `uDeg23 l`.** -/
theorem polyCoverAt_class23 (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDeg23 l)) (uExp (classV Kc pc l) (uDeg23 l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDeg23
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · obtain ⟨C⟩ := splitUniformClass_all_fejer Kc pc hK hp hlem l hl
    have hfit := split_pair_fejer_le_uDeg23 hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDeg23 l) (by omega) (by omega)
      (by omega)
    refine P0.weaken ?_ ?_ ?_
    · intro g t s hg hg1 ht ht1 hs hs1
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
    · intro g t s _ _ _ _ _ _
      exact (uExp_pos_le _ _ g t s).1
    · intro g t s hg hg1 ht ht1 hs hs1
      show (uCount _ _ g t s)⁻¹ ≤ _
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]

end LeanProofs.GowersSzemeredi
