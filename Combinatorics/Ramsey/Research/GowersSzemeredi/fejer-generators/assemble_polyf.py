"""Proofs16PolynomialFejer: Theorem 16.2 / Corollary 16.11 with polynomial controls at the Fejér classes."""
import re
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')


def text(name):
    return (GS / f'{name}.lean').read_text(encoding='utf-8')


def between(t, start, end_marker):
    a = t.index(start)
    b = t.index(end_marker, a + len(start))
    return t[a:b]


st = text('Proofs16PolynomialStructure')
co = text('Proofs16PolynomialCorollary')
p16 = between(st, '/-- **Theorem 16.2 with polynomial controls in every dimension**, from the',
              '/-- **The polynomial form implies the printed Theorem 16.2** in dimension `k`. -/')
cor = between(co, '/-- The localization parameter is at most the box density. -/', 'end LeanProofs.GowersSzemeredi')
body = p16 + cor
body = body.replace('uDeg68', 'uDeg23').replace('68 * 2 ^', '23 * 2 ^').replace('236 * 2 ^ k + k + 24', '101 * 2 ^ k + k + 24')
REN = [('theorem_16_2_polynomial_of_profiles', 'theorem_16_2_polynomial_fejer_of_profiles'),
       ('corollary_16_11_polynomial_of_profiles', 'corollary_16_11_polynomial_fejer_of_profiles'),
       ('singlePieceEtaC_le_density', 'singlePieceEtaF_le_density'), ('expDegC_tight_le', 'expDegF_tight_le'),
       ('singlePieceGlobalDensityC_pos', 'singlePieceGlobalDensityF_pos'),
       ('singlePieceGlobalDensityC', 'singlePieceGlobalDensityF'), ('singlePieceEtaC', 'singlePieceEtaF'),
       ('GenParamsC', 'GenParamsF'), ('expDegC', 'expDegF'), ('rhoDegC', 'rhoDegF'),
       ('Eloc_inv_leC', 'Eloc_inv_leF'), ('yIn_boundsC', 'yIn_boundsF'),
       ('tightHyp_of_profiles', 'tightHyp_of_profiles_fejer'), ('polyCoverAt_class68', 'polyCoverAt_class23'),
       ('single_piece_frequency_box_global_cover', 'single_piece_frequency_box_global_cover_fejer')]
for a, b in REN:
    body = re.sub(r'\b' + a + r'\b', b, body)
body = body.replace('(`polyCoverAt_class68`)', '(`polyCoverAt_class23`)')
bad = [l for l in body.split('\n') if re.search(r'GenParamsC|uDeg68|class68|\b68\b|\b236\b|\w+C\b', l)
       and not re.search(r'P\.CHyp|\bCHyp\b', l)]
assert not bad, bad

HEADER = '''import GowersSzemeredi.Proofs16PolynomialCorollary
import GowersSzemeredi.Proofs18CoverFejerHeadline

/-! **Theorem 16.2 and Corollary 16.11 with polynomial controls at the Fejér
classes** (Notes L.16e).

The Fejér instances of `Proofs16PolynomialStructure` and
`Proofs16PolynomialCorollary` (generated):
* `theorem_16_2_polynomial_fejer_of_profiles`: graph count
  `max(1, (4V/(γθρ))^(2^(23·2^k)))` with `V = 2^(2^(2^(k+4)+1))`, and width
  exponent its inverse, in every dimension `k ≥ 1` (printed route:
  `2^(68·2^k)`). `theorem162At_of_polynomial_fejer`: it implies the printed
  Theorem 16.2.
* `corollary_16_11_polynomial_fejer_of_profiles` and `expDegF_tight_le`:
  Corollary 16.11 with `e⁻¹ ≤ (2/α)^(2^(101·2^k + k + 24))` (printed route:
  `236·2^k + k + 24`; printed statement: `e⁻¹ = exp(poly(1/α))`). -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem uDeg23_le_uDeg68 (k : Nat) : uDeg23 k ≤ uDeg68 k := by
  unfold uDeg23 uDeg68
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

'''
TAIL = '''
/-- **The Fejér polynomial form implies the printed Theorem 16.2** in dimension `k`. -/
theorem theorem162At_of_polynomial_fejer {k : Nat}
    (h : PolyCoverAt k (uCount (2 ^ (2 ^ tightMuV k)) (uDeg23 k))
      (uExp (2 ^ (2 ^ tightMuV k)) (uDeg23 k))) : Theorem162At k :=
  theorem162At_of_polynomial (h.uniform_mono (one_le_pow₀ (by norm_num)) le_rfl (uDeg23_le_uDeg68 k))

end LeanProofs.GowersSzemeredi
'''
out = HEADER + body + TAIL
(GS / 'Proofs16PolynomialFejer.lean').write_text(out, encoding='utf-8', newline='\n')
print('wrote', len(out.splitlines()))
