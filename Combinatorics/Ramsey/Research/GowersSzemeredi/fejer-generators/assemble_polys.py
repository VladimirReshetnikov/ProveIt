"""Proofs16PolynomialFejerS: polynomial Theorem 16.2 / Corollary 16.11 at (sDeg, tightMu0S)."""
import re, importlib.util
from pathlib import Path

SP = Path(r'C:\Users\vresh\AppData\Local\Temp\claude\C--ProveIt--claude-worktrees-q-fabius-deformations-merge-9bc27b\91437c4c-e56c-4ce0-b990-4cbd116b50cf\scratchpad')
GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
src = (SP / 'assemble_s.py').read_text(encoding='utf-8')
ns = {}
exec(src.split('# --- Modulus')[0], ns)          # RENAMES, rename, BAD, check
s = (GS / 'Proofs16PolynomialFejerQ.lean').read_text(encoding='utf-8')
a = s.index('/-- **Theorem 16.2 with polynomial controls in every dimension**')
b = s.index('/-- **The polynomial form at `uDegQ` implies the printed Theorem 16.2.** -/')
body = s[a:b]
OLD = '58 * 2 ^ k + 9 * (k + 4) ^ 2 + k + 30'
assert OLD not in body   # the closed form lives in the header lemma and the bridge
for x, y in [('theorem_16_2_polynomial_fejerQ_of_profiles', 'theorem_16_2_polynomial_fejerS_of_profiles'),
             ('corollary_16_11_polynomial_fejerQ_of_profiles', 'corollary_16_11_polynomial_fejerS_of_profiles'),
             ('expDegQ_tight_le', 'expDegS_tight_le')]:
    body = re.sub(r'\b' + x + r'\b', y, body)
body = ns['rename'](body)
ns['check']('Proofs16PolynomialFejerS', body)

HEADER = '''import GowersSzemeredi.Proofs16PolynomialFejerQ
import GowersSzemeredi.Proofs18CoverFejerHeadlineS

/-! **Theorem 16.2 and Corollary 16.11 with polynomial controls at the classes
from the small dimension-two seed** (Notes L.16j).

The `(sDeg, tightMu0S)` instances of `Proofs16PolynomialFejerQ` (generated):
* `theorem_16_2_polynomial_fejerS_of_profiles`: graph count
  `max(1, (4V/(γθρ))^uDegS k)` with `log₂ uDegS k = 4·2^k + 3(k+4)² + 32`
  (with additive slack `14·2^k + 3(k+4)² + 2`, the Fejér classes `23·2^k`,
  the printed route `68·2^k`), which implies the printed Theorem 16.2 for
  `k ≥ 1` (`theorem162At_of_polynomial_fejerS`);
* `corollary_16_11_polynomial_fejerS_of_profiles` with `expDegS_tight_le`:
  `e⁻¹ ≤ (2/α)^(2^(32·2^k + 9(k+4)² + k + 120))` (additive slack:
  `58·2^k`; printed route `236·2^k`). The leading `32·2^k` is the
  `genMuK k + 2` branch of the exponent degree; the density branch is
  `28·2^k`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem uDegS_le_uDeg68 {k : Nat} (hk : 1 ≤ k) : uDegS k ≤ uDeg68 k := by
  unfold uDegS uDeg68
  refine Nat.pow_le_pow_right (by norm_num) ?_
  rcases Nat.lt_or_ge k 4 with h | h
  · interval_cases k <;> norm_num
  · have h1 := sq_le_two_pow_four k h
    have h2 : 16 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) h)
    omega

/-- The exponent degree at `(sDeg, tightMu0S)`, in closed form. -/
theorem expDegS_tight_le {k : Nat} (hk : 1 ≤ k) :
    GenParamsS.expDegS k (tightMu0S k) (genMuK k) + 3 ≤ 32 * 2 ^ k + 9 * (k + 4) ^ 2 + k + 120 := by
  unfold GenParamsS.expDegS GenParamsS.rhoDegS tightMu0S tightMuV genMuK sDeg
  rw [fixDegQ_eq hk, two_pow_five_mul, two_pow_four_mul]
  have := Nat.lt_two_pow_self (n := k)
  generalize (k + 4) ^ 2 = s
  generalize 2 ^ k = x at *
  omega

'''
TAIL = '''
/-- **The polynomial form at `uDegS` implies the printed Theorem 16.2.** -/
theorem theorem162At_of_polynomial_fejerS {k : Nat} (hk : 1 ≤ k)
    (h : PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDegS k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDegS k))) : Theorem162At k :=
  theorem162At_of_polynomial (h.uniform_mono (one_le_pow₀ (by norm_num)) le_rfl (uDegS_le_uDeg68 hk))

end LeanProofs.GowersSzemeredi
'''
out = HEADER + body + TAIL
(GS / 'Proofs16PolynomialFejerS.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
