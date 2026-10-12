"""Proofs16PolynomialFejerX: polynomial Theorem 16.2 / Corollary 16.11 at the X classes (Notes L.16n)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs16PolynomialFejerS.lean').read_text(encoding='utf-8')
a = s.index('/-- **Theorem 16.2 with polynomial controls in every dimension**')
b = s.index('/-- **The polynomial form at `uDegS` implies the printed Theorem 16.2.** -/')
body = s[a:b]
TOWER = '(hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ ((2 : Nat) ^ (k + 5))))'
POLY = '(hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16)))'
assert body.count(TOWER) == 2
body = body.replace(TOWER, POLY)
body = body.replace('(classV_le_tight Kc pc hconst k)', '(classV_le_poly Kc pc hconst k)')
for x, y in [('theorem_16_2_polynomial_fejerS_of_profiles', 'theorem_16_2_polynomial_fejerX_of_profiles'),
             ('corollary_16_11_polynomial_fejerS_of_profiles', 'corollary_16_11_polynomial_fejerX_of_profiles'),
             ('uDegS', 'uDegX'), ('sDeg', 'tDegX'), ('tightMuV', 'tightMuW'), ('GenParamsS', 'GenParamsX'),
             ('expDegS', 'expDegX'), ('rhoDegS', 'rhoDegX'), ('tightMu0S', 'tightMu0X'), ('genMuK', 'genMuKX'),
             ('tightHyp_of_profiles_fejerS', 'tightHyp_of_profiles_fejerX'), ('polyCoverAt_classS', 'polyCoverAt_classX'),
             ('Eloc_inv_leS', 'Eloc_inv_leX'), ('yIn_boundsS', 'yIn_boundsX')]:
    body = re.sub(r'\b' + x + r'\b', y, body)
bad = [l for l in body.split('\n') if re.search(r'\b\w*S\b(?<!fejerS)|classV_le_tight|tightMuV\b|\bgenMuK\b|sDeg', l)
       and not re.search(r'GowersSzemeredi|Section16|PolyCoverAt|IsMultilinear|DiscValued|AbstractFamily|Retiled', l)]
bad = [l for l in bad if re.search(r'\b(?:\w+S|sDeg|uDegS|tightMuV|genMuK|classV_le_tight)\b', l)]
assert not bad, bad[:8]

HEADER = '''import GowersSzemeredi.Proofs16PolynomialFejerS
import GowersSzemeredi.Proofs18CoverFejerHeadlineX

/-! **Theorem 16.2 and Corollary 16.11 with polynomial controls at the classes of
constant `5/2` and the polynomial base budget** (Notes L.16n).

The X instances of `Proofs16PolynomialFejerS` (generated), from the profiles
with polynomial family constants:
* `theorem_16_2_polynomial_fejerX_of_profiles`: graph count
  `max(1, (4V/(γθρ))^uDegX k)` with `V = 2^(2^(4k+13))` and `log₂ uDegX k = tDegX k`.
  This is the exact table up to `k = 12` and `5·2^(k−1) + 3(k+4)² + 2` beyond,
  against `4·2^k + 3(k+4)² + 32` at the S classes and `68·2^k` printed. It
  implies the printed Theorem 16.2 for `k ≥ 1` (`theorem162At_of_polynomial_fejerX`).
* `corollary_16_11_polynomial_fejerX_of_profiles` with `expDegX_tight_le`:
  `e⁻¹ ≤ (2/α)^(2^(3·tDegX k + 6k + 38))`, that is `7.5·2^k + O(k²)`, against
  `32·2^k` at the S classes and `236·2^k` printed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem uDegX_le_uDeg68 {k : Nat} (hk : 1 ≤ k) : uDegX k ≤ uDeg68 k := by
  unfold uDegX uDeg68
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rcases Nat.lt_or_ge k 13 with h | h
  · interval_cases k <;> decide
  · rw [tDegX_eq_of_ge h]
    have h1 := sq_le_two_pow_four k (by omega)
    have h2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [show k = (k - 1) + 1 by omega, pow_succ]; simp; ring
    have h3 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
    omega

/-- The exponent degree at `(tDegX, tightMu0X)`. -/
theorem expDegX_tight_le (k : Nat) :
    GenParamsX.expDegX k (tightMu0X k) (genMuKX k) + 3 ≤ 3 * tDegX k + 6 * k + 38 := by
  unfold GenParamsX.expDegX GenParamsX.rhoDegX tightMu0X tightMuW genMuKX pDeg
  have := seventeen_le_tDegX k
  have hkt : k ≤ tDegX k := by
    rcases Nat.lt_or_ge k 13 with h | h
    · interval_cases k <;> decide
    · rw [tDegX_eq_of_ge h]
      have : k ≤ (k + 4) ^ 2 := by nlinarith
      omega
  simp only [max_def]
  split_ifs <;> omega

theorem tightMuW_le_tightMuV (k : Nat) : tightMuW k ≤ tightMuV k := by
  unfold tightMuW tightMuV
  have h := Nat.lt_two_pow_self (n := k)
  have h16 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
  omega

'''
TAIL = '''
/-- **The polynomial form at `uDegX` implies the printed Theorem 16.2.** -/
theorem theorem162At_of_polynomial_fejerX {k : Nat} (hk : 1 ≤ k)
    (h : PolyCoverAt k (uCount (2 ^ (2 ^ tightMuW k)) (uDegX k))
      (uExp (2 ^ (2 ^ tightMuW k)) (uDegX k))) : Theorem162At k :=
  theorem162At_of_polynomial (h.uniform_mono (one_le_pow₀ (by norm_num))
    (pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) (tightMuW_le_tightMuV k)))
    (uDegX_le_uDeg68 hk))

end LeanProofs.GowersSzemeredi
'''
out = HEADER + body + TAIL
(GS / 'Proofs16PolynomialFejerX.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
