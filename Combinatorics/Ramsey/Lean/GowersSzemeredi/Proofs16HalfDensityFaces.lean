import GowersSzemeredi.Proofs16AllFaceInduction

/-! The deletion budget in Lemma 16.4: pruning every proper direction
with parameter 2^(-(k+2))*theta retains at least half the starting density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem restrict_proper_faces_half_density (k : Nat)
    (hth : ∀ l, 1 ≤ l → l ≤ k → Theorem162At l) (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        theta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (theta / 2) * (N : Real) ^ (k + 1) ≤ B'.card ∧
          ∀ l, 1 ≤ l → l ≤ k → ∀ F : CoordinateFace N (k + 1) l,
            MultiplyLinearFunction gamma
              (gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma l)
              (F.domain B') (F.pullback phi) := by
  let eps := (2 : Real) ^ (-(k + 2 : Real)) * theta
  have hpow : (2 : Real) ^ (-(k + 2 : Real)) = ((2 : Real) ^ (k + 2))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    congr 1
    simpa only [Nat.cast_add, Nat.cast_ofNat] using (Real.rpow_natCast (2 : Real) (k + 2))
  have heps : 0 < eps := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) ht
  have heps1 : eps ≤ 1 := by
    have hfac : (2 : Real) ^ (-(k + 2 : Real)) ≤ 1 := by
      rw [hpow]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    exact (mul_le_of_le_one_left ht.le hfac).trans ht1
  have hbudget : (2 : Real) ^ (k + 1) * eps = theta / 2 := by
    dsimp [eps]
    rw [hpow, show k + 2 = (k + 1) + 1 by omega, pow_succ]
    field_simp
    simp [pow_succ, mul_assoc]
  obtain ⟨N0, hN0⟩ := restrict_all_positive_proper_faces (k + 1)
    (fun l hl hlk => hth l hl (by omega)) gamma eps hg hg1 heps heps1
  refine ⟨N0, ?_⟩
  intro N _ _ hN B phi hB hprod
  obtain ⟨B', hsub, hcard, hfaces⟩ := hN0 N hN B phi hprod
  refine ⟨B', hsub, ?_, fun l hl hlk F => hfaces l hl (by omega) F⟩
  rw [hbudget] at hcard
  linarith

end LeanProofs.GowersSzemeredi
