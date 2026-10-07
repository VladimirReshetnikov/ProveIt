import GowersSzemeredi.Proofs16AlphabetCoverParameters

/-! Finite-alphabet witnesses for the all-box line-cover premise. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem finiteAlphabet_allBoxLineCovers {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (S : Finset (ZMod N)) (hphi : ∀ z ∈ B, phi z ∈ S)
    {theta gamma : Real} (hθ : 0 < theta) (hθ1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 1 ≤ section16Lemma9R theta gamma k)
    (hS : ∀ sigma : Real, 0 < sigma → sigma ≤ 1 →
      (S.card : Real) ≤ section16Lemma9QBound sigma theta gamma k) :
    Section16AllBoxLineCovers theta gamma B phi := by
  intro sigma hs hs1 m P hP hm
  obtain ⟨hth, hth1, hd, hd1⟩ := section16_theta_delta_bounds k hθ hθ1 hg hg1
  have ht := section16T_one_le k hd hd1 hth hth1
  obtain ⟨_, _, hqD⟩ := alphabet_cover_controls k hs hs1 hd hd1 ht
  refine ⟨S.card, 1, hS sigma hs hs1, ?_, ?_⟩
  · simpa only [section16Lemma9DeltaQBound, Nat.cast_one] using hqD
  · apply finiteAlphabet_section16LineCover P hP B phi S hphi hs.le
    obtain ⟨hz, hzhalf⟩ := section16Zeta_pos_le_half k hθ hθ1 hg hg1
    exact (section16Lemma9Width_le_scale m 1 k hs hs1 hg hg1 hd hd1 hr ht hz.le
      (by linarith)).trans (by exact_mod_cast hm)

theorem section16Lemma9R_unit_one_ge_eight : 8 ≤ section16Lemma9R 1 1 1 := by
  have harg : (2 : Real) ^ (-(1 + 2 : Real)) * 1 = 1 / 8 := by norm_num
  have hbase : (16 : Real) ≤ multipleS (1 / 8) 1 1 := by
    unfold multipleS
    norm_num only [one_div, mul_one, div_inv_eq_mul, mul_one]
    exact le_self_pow₀ (by norm_num) (by positivity)
  simpa only [section16Lemma9R, harg, one_zpow, mul_one, Nat.pow_one,
    Nat.reduceSub, Nat.cast_one, one_mul] using (show (8 : Real) ≤ multipleS (1 / 8) 1 1 by linarith)

theorem finiteAlphabet_allBoxLineCovers_unit {N : Nat} [NeZero N]
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (S : Finset (ZMod N)) (hphi : ∀ z ∈ B, phi z ∈ S)
    (hS : (S.card : Real) ≤ 8 * multipleQ (1 / 2) 1 2) :
    Section16AllBoxLineCovers 1 1 B phi := by
  have hr8 := section16Lemma9R_unit_one_ge_eight
  have hr : 1 ≤ section16Lemma9R 1 1 1 := by linarith
  apply finiteAlphabet_allBoxLineCovers B phi S hphi (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hr
  intro sigma hs hs1
  apply hS.trans
  exact (mul_le_mul_of_nonneg_right hr8 (by unfold multipleQ multipleC; positivity)).trans
    (alphabet_q_bound_amplification 2 hs hs1 hr)

end LeanProofs.GowersSzemeredi
