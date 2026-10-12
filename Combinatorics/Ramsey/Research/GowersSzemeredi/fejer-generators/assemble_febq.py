"""Proofs18FejerEnvelopeBaseQ: the Fejér fixed-parameter bounds at fixDegQ k = fixDeg (k - 1)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs18GenericEnvelopeBase.lean').read_text(encoding='utf-8')
a = s.index('theorem thetaTwo_gen_bounds')
b = s.index('/-- **The Bohr radius**')
body = s[a:b]
body = body.replace('section16ThetaTwo_pos_le (gamma := alpha / 2) k ha ha1 (half_pos ha)\n    (by linarith)',
                    'section16ThetaTwo_pos_le_with (fejer_alpha_bounds k ha ha2).1 (fejer_alpha_bounds k ha ha2).2')
body = body.replace('section16_theta_delta_bounds k ha ha1 (half_pos ha) (by linarith)',
                    'section16_theta_delta_bounds_with (fejer_alpha_bounds k ha ha2).1 (fejer_alpha_bounds k ha ha2).2')
body = body.replace('thetaOne_gen_bounds k ha ha2', 'thetaOne_fejer_bounds k ha ha2')
body = body.replace('section16ThetaOne alpha (alpha / 2) k', 'fejerThetaOne alpha (alpha / 2) k')
body = body.replace('globalBudget alpha (alpha / 2) k', 'globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k')
body = body.replace('globalTheta2 alpha (alpha / 2) k', 'globalTheta2W (fejerThetaOne alpha (alpha / 2) k)')
body = body.replace('unfold globalBudget\n', 'unfold globalBudgetW\n').replace('unfold globalTheta2\n', 'unfold globalTheta2W\n')
body = body.replace('2 ^ fixDeg k', '2 ^ (5 * k + 21)')
body = body.replace('unfold fixDeg; exact this', 'exact this').replace('  unfold fixDeg\n', '')
body = body.replace('''          have : 5 ≤ 2 ^ (k + 5) := by
            calc 5 ≤ 2 ^ 5 := by norm_num
              _ ≤ 2 ^ (k + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega)''', '''          omega)''')
body = body.replace('2 ^ (k + 5)', '(5 * k + 14)')
body = body.replace('def fixDeg (k : Nat) : Nat := (5 * k + 14) + 7\n', '')
body = re.sub(r'/-- The log-degree of the fixed parameters of dimension `k`. -/\n', '', body)
for x, y in [('thetaTwo_gen_bounds', 'thetaTwo_fejer_bounds'), ('budget_gen_bounds', 'budget_fejer_bounds5'),
             ('T2_gen_bounds', 'T2_fejer_bounds5'), ('delta_gen_bounds', 'delta_fejer_bounds5')]:
    body = re.sub(r'\b' + x + r'\b', y, body)
bad = [l for l in body.split('\n') if re.search(r'section16ThetaOne|fixDeg|\bglobalBudget\b|\bglobalTheta2\b|2 \^ \(k \+ 5\)', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs18FejerEnvelopeBase

/-! **The Fejér fixed parameters at the base budget of `V`** (Notes L.16i).

`Proofs18FejerEnvelopeBase` transfers the printed bounds at
`X^(2^fixDeg k)`, `fixDeg k = 2^(k+5) + 7`, which keeps the base budget at
`μ₀ ≈ 32·2^k`. The Fejér density is much larger: `θ₁′⁻¹ ≤ X^(2^(5k+16))`
(`thetaOne_fejer_bounds`, from `F ≤ 2^(5k+14)`). So the budget, `θ₂/2` and δ
are above `X^(-2^(5k+21))` (`…_fejer_bounds5`, generated from the printed
proofs with the atom `2^(k+5)` replaced by `5k + 14`), and hence above
`X^(-2^fixDegQ k)` with

  `fixDegQ k = fixDeg (k − 1) = 2^(k+4) + 7`   (k ≥ 1),

the size of the class-base term `tightMuV k = 2^(k+4) + 1`. Stating it as
`fixDeg (k − 1)` lets every generic step lemma be reused at `k − 1`.
* `budget_gen_bounds_fejerQ`, `T2_gen_bounds_fejerQ`,
  `delta_gen_bounds_fejerQ`;
* `baseCFQ_recipPowerLB`: `baseCF_recipPowerLB` at `fixDegQ`;
* `fixDeg_le_two_fixDegQ`, `k_succ_le_two_pow_fixDegQ`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The base-budget log-degree at the class base: `fixDeg (k − 1)`. -/
def fixDegQ (k : Nat) : Nat := fixDeg (k - 1)

theorem fixDegQ_eq {k : Nat} (hk : 1 ≤ k) : fixDegQ k = 2 ^ (k + 4) + 7 := by
  unfold fixDegQ fixDeg
  rw [show k - 1 + 5 = k + 4 by omega]

theorem fixDeg_le_two_fixDegQ (k : Nat) : fixDeg k ≤ 2 * fixDegQ k := by
  unfold fixDegQ fixDeg
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · rw [show k - 1 + 5 = k + 4 by omega, show k + 5 = (k + 4) + 1 by ring, pow_succ]
    omega

theorem five_k_le_fixDegQ (k : Nat) : 5 * k + 21 ≤ fixDegQ k := by
  unfold fixDegQ fixDeg
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · norm_num
  · rw [show k - 1 + 5 = k + 4 by omega]
    have h : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    have h16 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
    omega

theorem k_succ_le_two_pow_fixDegQ (k : Nat) : k + 1 ≤ 2 ^ fixDegQ k := by
  have h1 : k + 1 ≤ 2 ^ (5 * k + 21) := by
    have := Nat.lt_two_pow_self (n := 5 * k + 21); omega
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) (five_k_le_fixDegQ k))

section Fixed

variable {alpha : Real}

/-- `θ₁′⁻¹ ≤ X^(2^(5k+16))`. -/
theorem thetaOne_fejer_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < fejerThetaOne alpha (alpha / 2) k ∧ fejerThetaOne alpha (alpha / 2) k ≤ 1 ∧
      (fejerThetaOne alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (5 * k + 16)) := by
  obtain ⟨h0, h1⟩ := fejer_alpha_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  have hq0 : 0 < alpha * (alpha / 2) / 4 := by positivity
  refine ⟨by linarith, by linarith, ?_⟩
  unfold fejerThetaOne
  rw [← inv_pow]
  have hq := quarter_base_inv_le ha ha2
  have hF := fejerProductExponent_le k
  calc (alpha * (alpha / 2) / 4)⁻¹ ^ fejerProductExponent k
      ≤ ((2 / alpha) ^ 3) ^ fejerProductExponent k := pow_le_pow_left₀ (inv_pos.mpr hq0).le hq _
    _ = (2 / alpha) ^ (3 * fejerProductExponent k) := by rw [← pow_mul]
    _ ≤ (2 / alpha) ^ (2 ^ (5 * k + 16)) := by
        apply pow_le_pow_right₀ (le_trans (by norm_num) hX)
        have h : 2 ^ (5 * k + 16) = 4 * 2 ^ (5 * k + 14) := by
          rw [show 5 * k + 16 = (5 * k + 14) + 2 by ring, pow_add]; ring
        omega

'''
TAIL = '''
theorem budget_gen_bounds_fejerQ (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ∧
      globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ≤ 1 ∧
      (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDegQ k) := by
  obtain ⟨h0, h1, hi⟩ := budget_fejer_bounds5 k ha ha2
  exact ⟨h0, h1, pw_mono (two_div_ge_two ha ha2) hi (five_k_le_fixDegQ k)⟩

theorem T2_gen_bounds_fejerQ (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ∧
      globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (globalTheta2W (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDegQ k) := by
  obtain ⟨h0, h1, hi⟩ := T2_fejer_bounds5 k ha ha2
  exact ⟨h0, h1, pw_mono (two_div_ge_two ha ha2) hi (five_k_le_fixDegQ k)⟩

theorem delta_gen_bounds_fejerQ (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Delta (fejerThetaOne alpha (alpha / 2) k) ∧
      section16Delta (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16Delta (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDegQ k) := by
  obtain ⟨h0, h1, hi⟩ := delta_fejer_bounds5 k ha ha2
  exact ⟨h0, h1, pw_mono (two_div_ge_two ha ha2) hi (five_k_le_fixDegQ k)⟩

/-- **The Fejér base density is a reciprocal power, at `fixDegQ`.** -/
theorem baseCFQ_recipPowerLB {V : Real} {D k μV μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDegQ k) + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha) (baseCF V D k alpha) (D * 2 ^ μ0 + 1) (D + 1) := by
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejerQ k ha ha2
  have hc := GenParams.slice_const_le (V := V) (B := globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)
    (μV := μV) (k := k - 1) (μ0 := μ0) ha ha2 hV hVμ hB0 hBi hμ0
  intro s hs hs1
  have hs2 : 0 < s / 2 := half_pos hs
  have hs21 : s / 2 ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := half_pos ha
  have hg1 : alpha / 2 ≤ 1 := by linarith
  set B := globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k with hBdef
  have hQ1 := one_le_uCount V D (alpha / 2) B (s / 2)
  have hQ0 : 0 < uCount V D (alpha / 2) B (s / 2) := lt_of_lt_of_le zero_lt_one hQ1
  have hQeq := uCount_eq hV D hg hg1 hB0 hB1 hs2 hs21
  rw [GenParams.uniformBase_slice V ha hB0 hs] at hQeq
  show 0 < s / 2 / uCount V D (alpha / 2) B (s / 2) ∧
    s / 2 / uCount V D (alpha / 2) B (s / 2) ≤ 1 ∧
    (s / 2 / uCount V D (alpha / 2) B (s / 2))⁻¹ ≤
      (2 / alpha) ^ (D * 2 ^ μ0 + 1) * s⁻¹ ^ (D + 1)
  refine ⟨div_pos hs2 hQ0, (div_le_one hQ0).mpr (by linarith), ?_⟩
  rw [inv_div, hQeq]
  set X := 2 / alpha with hXdef
  have hsi : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hcs : 8 * V * X * B⁻¹ * s⁻¹ ≤ X ^ (2 ^ μ0) * s⁻¹ := mul_le_mul_of_nonneg_right hc hsi
  have hpow := pow_le_pow_left₀ (by positivity) hcs D
  have h2X : (2 : Real) ≤ X ^ 1 := by rw [pow_one]; exact hX
  calc (8 * V * X * B⁻¹ * s⁻¹) ^ D / (s / 2) = 2 * (s⁻¹ * (8 * V * X * B⁻¹ * s⁻¹) ^ D) := by
        rw [div_eq_mul_inv, inv_div]; ring
    _ ≤ X ^ 1 * (s⁻¹ * (X ^ (2 ^ μ0) * s⁻¹) ^ D) :=
        mul_le_mul h2X (mul_le_mul_of_nonneg_left hpow hsi) (by positivity) (by positivity)
    _ = X ^ (D * 2 ^ μ0 + 1) * s⁻¹ ^ (D + 1) := by ring

end Fixed

end LeanProofs.GowersSzemeredi
'''
out = HEADER + body + TAIL
(GS / 'Proofs18FejerEnvelopeBaseQ.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
