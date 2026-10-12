"""Proofs16PolynomialFejerQ: polynomial Theorem 16.2 / Corollary 16.11 at (qDeg, fixDegQ)."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
s = (GS / 'Proofs16PolynomialFejer.lean').read_text(encoding='utf-8')


def between(t, a, b):
    i = t.index(a)
    return t[i:t.index(b, i + len(a))]


p16 = between(s, '/-- **Theorem 16.2 with polynomial controls in every dimension**, from the',
              '/-- The localization parameter is at most the box density. -/')
cor = between(s, '/-- **Corollary 16.11 with polynomial exponents in dimension `k + 1`**, from',
              '/-- **The Fejér polynomial form implies the printed Theorem 16.2**')
body = p16 + cor
ETA_OLD = '    show 0 < singlePieceEtaF _ alpha P.k\n    unfold singlePieceEtaF; positivity\n'
assert ETA_OLD in body
body = body.replace(ETA_OLD, '    exact singlePieceEtaF_pos ha (by linarith) hQb\n')
body = body.replace('101 * 2 ^ k + k + 24', '58 * 2 ^ k + 9 * (k + 4) ^ 2 + k + 30')
body = re.sub(r'23 \* 2 \^ (k|P\.k)\b', r'qDeg \1', body)
for a, b in [('theorem_16_2_polynomial_fejer_of_profiles', 'theorem_16_2_polynomial_fejerQ_of_profiles'),
             ('corollary_16_11_polynomial_fejer_of_profiles', 'corollary_16_11_polynomial_fejerQ_of_profiles'),
             ('GenParamsF', 'GenParamsQ'), ('expDegF', 'expDegQ'), ('rhoDegF', 'rhoDegQ'),
             ('Eloc_inv_leF', 'Eloc_inv_leQ'), ('yIn_boundsF', 'yIn_boundsQ'),
             ('tightHyp_of_profiles_fejer', 'tightHyp_of_profiles_fejerQ'), ('tightMu0', 'tightMu0Q'),
             ('polyCoverAt_class23', 'polyCoverAt_classQ'), ('uDeg23', 'uDegQ')]:
    body = re.sub(r'\b' + a + r'\b', b, body)
bad = [l for l in body.split('\n') if re.search(r'uDeg23|class23|GenParamsF|expDegF|rhoDegF|\b23 \*|\b101\b', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs16PolynomialFejer
import GowersSzemeredi.Proofs18CoverFejerHeadlineQ

/-! **Theorem 16.2 and Corollary 16.11 with polynomial controls at the classes
with additive slack** (Notes L.16i).

The `(qDeg, fixDegQ)` instances of `Proofs16PolynomialFejer` (generated):
* `theorem_16_2_polynomial_fejerQ_of_profiles`: graph count
  `max(1, (4V/(γθρ))^uDegQ k)` with `log₂ uDegQ k = 14·2^k + 3(k+4)² + 2`
  (the Fejér classes give `23·2^k`, the printed route `68·2^k`), which
  implies the printed Theorem 16.2 (`theorem162At_of_polynomial_fejerQ`);
* `corollary_16_11_polynomial_fejerQ_of_profiles` with `expDegQ_tight_le`:
  `e⁻¹ ≤ (2/α)^(2^(58·2^k + 9(k+4)² + k + 30))` (Fejér classes: `101·2^k`;
  printed route `236·2^k`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem uDegQ_le_uDeg68 (k : Nat) : uDegQ k ≤ uDeg68 k := by
  unfold uDegQ uDeg68
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rcases Nat.lt_or_ge k 4 with h | h
  · interval_cases k <;> norm_num
  · have h1 := sq_le_two_pow_four k h
    have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

/-- The exponent degree at `(qDeg, tightMu0Q)`, in closed form. -/
theorem expDegQ_tight_le {k : Nat} (hk : 1 ≤ k) :
    GenParamsQ.expDegQ k (tightMu0Q k) (genMuK k) + 3 ≤ 58 * 2 ^ k + 9 * (k + 4) ^ 2 + k + 30 := by
  unfold GenParamsQ.expDegQ GenParamsQ.rhoDegQ tightMu0Q tightMuV genMuK qDeg
  rw [fixDegQ_eq hk, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

'''
TAIL = '''
/-- **The polynomial form at `uDegQ` implies the printed Theorem 16.2.** -/
theorem theorem162At_of_polynomial_fejerQ {k : Nat}
    (h : PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDegQ k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDegQ k))) : Theorem162At k :=
  theorem162At_of_polynomial (h.uniform_mono (one_le_pow₀ (by norm_num)) le_rfl (uDegQ_le_uDeg68 k))

end LeanProofs.GowersSzemeredi
'''
out = HEADER + body + TAIL
(GS / 'Proofs16PolynomialFejerQ.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
